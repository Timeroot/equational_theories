import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pyx_pxy_pxx_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq75 X0 X0
       have r₂ := eq74 X0 X0
       grind)
    | (have r₁ := eq75 X1 X0
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq75 X1 X1
       have r₂ := eq74 X1 X1
       grind)
    | exact resolve eq75 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq75
  have eq123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79
    | (have j0 := eq79 (σ X1) (σ X0)
       grind)
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq147 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq142 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq142 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq142 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq142 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq155 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq123
    | (have j0 := eq123 X0 X1
       grind)
    | exact resolve eq123 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq123
  have eq530 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq12
    | (have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq550 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq530 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq563 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq550
    | (have j0 := eq550 X0 X1
       grind)
    | exact resolve eq550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq564 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq1023 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq564 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq3094 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq155 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq12
    | (have j1 := eq155 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq155 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq155 X0 X1
       grind)
    | exact resolve eq12 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq3104 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3094 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3094
  have eq3118 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3104 X0 X1
       have j1 := eq1023 X0 X1
       grind)
    | (have r₁ := eq3104 X0 X1
       have r₂ := eq1023 X0 X1
       grind)
    | exact resolve eq3104 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023 eq3104
  have eq3175 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3118 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3118
    | (have j0 := eq3118 X0 X1
       grind)
    | exact resolve eq3118 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118
  have eq3176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3175 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175
  have eq3298 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3176 x y
       grind)
    | exact superpose eq3176 eq16
    | exact resolve eq16 eq3176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176
  have eq3531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq3298
       have i₂ := eq147 y x
       grind)
    | exact superpose eq147 eq3298
    | (have j1 := eq147 x y
       grind)
    | exact resolve eq3298 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq3534 : (M.op x y) = (M.op y x) := by grind
  clear eq3531
  have eq4028 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3534
       grind)
    | exact superpose eq3534 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq3534
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3534
       grind)
    | exact resolve eq12 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534
  have eq4035 : (M.op x y) = (k y x) := by grind
  clear eq4028
  have eq4589 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq3298
       have i₂ := eq4035
       grind)
    | exact superpose eq4035 eq3298
    | exact resolve eq3298 eq4035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298 eq4035
  have eq4590 : False := by grind
  exact eq4590

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxy_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a b :=
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq60 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq60 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq12
    | (have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq60 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq191 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq199 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq363 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200
    | exact resolve eq200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq386 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq363
    | (have j0 := eq363 X0 X1
       grind)
    | exact resolve eq363 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq363
  have eq392 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq386
    | exact resolve eq386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq486 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq369
       have i₂ := eq392 x y
       grind)
    | exact superpose eq392 eq369
    | (have j1 := eq392 (σ x) (σ y)
       grind)
    | (have r₁ := eq369
       have r₂ := eq392 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq369
       have r₂ := eq392 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq369 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq392
  have eq489 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq486
  have eq529 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq489
       grind)
    | exact superpose eq489 eq10
    | exact resolve eq10 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq563 : x = y ∨ x = y := by
    first
    | (have i₁ := eq529
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq529
    | exact resolve eq529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq564 : x = y := by grind
  clear eq563
  have eq566 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq564
       grind)
    | exact superpose eq564 eq16
    | exact resolve eq16 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq567 : False := by grind
  exact eq567

/-- `Equation3927`: `x ◇ y = (x ◇ (y ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation3927 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3927 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3927.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq77 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq86
  have eq219 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq226 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq230 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq226 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq226 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq240 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       have j1 := eq77 X0 (σ X1)
       grind)
    | (have r₁ := eq230 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq230 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq230
  have eq248 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq240
    | (have j0 := eq240 X0 X1
       grind)
    | exact resolve eq240 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq249 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq253 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq249 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq249
    | exact resolve eq249 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq16
    | exact resolve eq16 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq316 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq253 X0 (τ X1)
       grind)
    | exact superpose eq253 eq17
    | exact resolve eq17 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq253
  have eq334 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq316
    | exact resolve eq316 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq343 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq334
    | exact resolve eq334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq360 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq264
       have i₂ := eq343 x y
       grind)
    | exact superpose eq343 eq264
    | exact resolve eq264 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq343
  have eq361 : False := by grind
  exact eq361

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_x_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq52 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) x X2
       have i₂ := eq14 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       have r₂ := eq14 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : (σ (k y (k y x))) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq37 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq37
    | exact resolve eq37 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (k x (k y y))) = (k (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq36 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq36
    | exact resolve eq36 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq80
    | (have j0 := eq80 (σ x) (σ X0)
       grind)
    | exact resolve eq80 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq94 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq80
    | (have j0 := eq80 (σ y) (σ X0)
       grind)
    | exact resolve eq80 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq98 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x x
       grind)
    | exact superpose eq80 eq44
    | (have j1 := eq80 x x
       grind)
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq80 y x
       grind)
    | exact superpose eq80 eq72
    | (have j1 := eq80 y x
       grind)
    | exact resolve eq72 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq80 y y
       grind)
    | exact superpose eq80 eq73
    | (have j1 := eq80 y y
       grind)
    | exact resolve eq73 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq370 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq52 X0 X2
       grind)
    | (have i₁ := eq52 X0 X2
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq110 eq80
    | (have j0 := eq80 (σ y) (σ x)
       grind)
    | exact resolve eq80 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq608
    | exact resolve eq608 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq612 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq609
       have r₂ := eq28
       grind)
    | exact resolve eq609 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq616 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq612
  have eq619 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq616
    | exact resolve eq616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq1198 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq619 eq110
    | exact resolve eq110 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq1201 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1198
  have eq1249 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 y X1 x
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq370
    | exact resolve eq370 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1254 : x ≠ y ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1201
       grind)
    | exact resolve eq13 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1486 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1249 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1249
    | (have j0 := eq1249 y X0
       grind)
    | exact resolve eq1249 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1573 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1486 X0
       grind)
    | (have i₁ := eq13 X0 x
       have i₂ := eq1486 X0
       grind)
    | exact superpose eq1486 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1486 (M.op x y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1486 X0
       grind)
    | exact resolve eq13 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1598 : (σ (k x (k y y))) = (M.op (k (σ y) (σ y)) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq93 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq93
    | exact resolve eq93 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1664 : (σ (k y (k y x))) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq94 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq94
    | exact resolve eq94 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq10968 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq1486 x
       grind)
    | exact superpose eq1486 eq98
    | exact resolve eq98 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq11023 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10968
    | exact resolve eq10968 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10968
  have eq11032 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11023 eq50
    | exact resolve eq50 eq11023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11023
  have eq11041 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq11032
    | exact resolve eq11032 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11032
  have eq11044 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1573 x
       grind)
    | (have r₁ := eq11041
       have r₂ := eq1573 (k x x)
       grind)
    | (have r₁ := eq11041
       have r₂ := eq1573 x
       grind)
    | exact resolve eq11041 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573 eq11041
  have eq11047 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11044
       grind)
    | exact superpose eq11044 eq44
    | exact resolve eq44 eq11044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11044
  have eq11073 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11047
    | exact resolve eq11047 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11047
  have eq11085 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11073
       have i₂ := eq80 sF2 sF2
       grind)
    | exact superpose eq80 eq11073
    | (have j1 := eq80 (σ x) (σ x)
       grind)
    | exact resolve eq11073 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11233 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq101
    | exact resolve eq101 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq11286 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11233
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11233
    | exact resolve eq11233 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11233
  have eq11294 : (τ (σ x)) = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11286 eq85
    | exact resolve eq85 eq11286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11286
  have eq11309 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq11294
    | exact resolve eq11294 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11294
  have eq11312 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11309
       have r₂ := eq1254
       grind)
    | exact resolve eq11309 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254 eq11309
  have eq11314 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11312
       grind)
    | exact superpose eq11312 eq73
    | exact resolve eq73 eq11312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11312
  have eq11339 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11314
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11314
    | exact resolve eq11314 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11314
  have eq11354 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11339
       have i₂ := eq80 sF3 sF3
       grind)
    | exact superpose eq80 eq11339
    | (have j1 := eq80 (σ y) (σ y)
       grind)
    | exact resolve eq11339 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12972 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11354 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq11354
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11354
       grind)
    | exact resolve eq13 eq11354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12973 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq11354
  have eq12974 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq12972
  have eq13030 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq12974 eq11339
    | exact resolve eq11339 eq12974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339 eq12974
  have eq13056 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq13030
  have eq13076 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13056
       have r₂ := eq12973
       grind)
    | exact resolve eq13056 eq12973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12973 eq13056
  have eq13091 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq13076 eq52
    | exact resolve eq52 eq13076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13076
  have eq13251 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq13091
    | (have j0 := eq13091 (σ y)
       grind)
    | exact resolve eq13091 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13091
  have eq14893 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11085 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq11085
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11085
       grind)
    | exact resolve eq13 eq11085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14894 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq11085
  have eq14895 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq14893
  have eq47446 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14895 eq11073
    | exact resolve eq11073 eq14895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11073 eq14895
  have eq47507 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq47446
  have eq47542 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq47507
       have r₂ := eq14894
       grind)
    | exact resolve eq47507 eq14894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14894 eq47507
  have eq47581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47542 eq13251
    | exact resolve eq13251 eq47542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13251 eq47542
  have eq47636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq47581
  have eq47654 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq47636
       have r₂ := eq28
       grind)
    | exact resolve eq47636 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47636
  have eq47659 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47654 eq63
    | (have r₁ := eq63
       have r₂ := eq47654
       grind)
    | exact resolve eq63 eq47654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq47654
  have eq47677 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq47659
  have eq48062 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47677 eq110
    | exact resolve eq110 eq47677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq47677
  have eq48073 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq48062
  have eq48083 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq48073
       grind)
    | exact superpose eq48073 eq101
    | exact resolve eq101 eq48073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq48089 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq52 y x
       have i₂ := eq48073
       grind)
    | exact superpose eq48073 eq52
    | exact resolve eq52 eq48073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48096 : x ≠ y ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq48073
       grind)
    | exact superpose eq48073 eq13
    | exact resolve eq13 eq48073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48073
  have eq48102 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq48083
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48083
    | exact resolve eq48083 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48083
  have eq48773 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq48089 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48089
    | (have j0 := eq48089 y
       grind)
    | exact resolve eq48089 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48089
  have eq49214 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq48773
       grind)
    | exact superpose eq48773 eq98
    | exact resolve eq98 eq48773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49279 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq48773
       grind)
    | exact superpose eq48773 eq13
    | exact resolve eq13 eq48773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48773
  have eq49319 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq49214
    | exact resolve eq49214 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49214
  have eq52681 : (τ (σ x)) = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq48102 eq85
    | exact resolve eq85 eq48102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq48102
  have eq52700 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq52681
    | exact resolve eq52681 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52681
  have eq52703 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq52700
       have r₂ := eq48096
       grind)
    | exact resolve eq52700 eq48096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48096 eq52700
  have eq52705 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq52703
       grind)
    | exact superpose eq52703 eq73
    | exact resolve eq73 eq52703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq52703
  have eq52745 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq52705
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52705
    | exact resolve eq52705 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq52705
  have eq52759 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq52745
       have i₂ := eq80 sF3 sF3
       grind)
    | exact superpose eq80 eq52745
    | (have j1 := eq80 (σ y) (σ y)
       grind)
    | exact resolve eq52745 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52892 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq49319 eq50
    | exact resolve eq50 eq49319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq49319
  have eq52914 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31 eq52892
    | exact resolve eq52892 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52892
  have eq52917 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq52914
       have r₂ := eq49279
       grind)
    | exact resolve eq52914 eq49279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49279 eq52914
  have eq52923 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq52917
       grind)
    | exact superpose eq52917 eq44
    | exact resolve eq44 eq52917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52917
  have eq52968 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq52923
    | exact resolve eq52923 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq52923
  have eq52984 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52968
       have i₂ := eq80 sF2 sF2
       grind)
    | exact superpose eq80 eq52968
    | (have j1 := eq80 (σ x) (σ x)
       grind)
    | exact resolve eq52968 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56892 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq52759 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq52759
       grind)
    | exact resolve eq13 eq52759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56893 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq52759
  have eq56894 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq56892
  have eq57061 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq56894 eq52745
    | exact resolve eq52745 eq56894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52745 eq56894
  have eq57076 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq57061
  have eq57112 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq57076
       have r₂ := eq56893
       grind)
    | exact resolve eq57076 eq56893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56893 eq57076
  have eq57149 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq57112 eq52
    | exact resolve eq52 eq57112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57152 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq57112 eq461
    | exact resolve eq461 eq57112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq57112
  have eq57361 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq57149
    | (have j0 := eq57149 (σ y)
       grind)
    | exact resolve eq57149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57149
  have eq57944 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq57152
    | (have j0 := eq57152 (σ y)
       grind)
    | exact resolve eq57152 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57152
  have eq67333 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq57361 eq52984
    | exact resolve eq52984 eq57361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52984 eq57361
  have eq67429 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq67333
  have eq67437 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq67429
       have r₂ := eq28
       grind)
    | exact resolve eq67429 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67429
  have eq67443 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq67437 eq28
    | exact resolve eq28 eq67437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67495 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq67437 eq57944
    | exact resolve eq57944 eq67437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57944 eq67437
  have eq67498 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq67495
  have eq70174 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq67498 eq52968
    | exact resolve eq52968 eq67498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52968 eq67498
  have eq70191 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq70174
  have eq70227 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq70191
       have r₂ := eq67443
       grind)
    | exact resolve eq70191 eq67443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67443 eq70191
  have eq70615 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq70227 eq27
    | exact resolve eq27 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70616 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq70227 eq30
    | exact resolve eq30 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq70786 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq70616
    | exact resolve eq70616 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq70616
  have eq70791 : y ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq70786 eq62
    | (have r₁ := eq62
       have r₂ := eq70786
       grind)
    | exact resolve eq62 eq70786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq70993 : y = (k y x) := by grind
  clear eq70791
  have eq71242 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq70993
       grind)
    | exact superpose eq70993 eq72
    | exact resolve eq72 eq70993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70993
  have eq71273 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq70227 eq71242
    | exact resolve eq71242 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71242
  have eq71289 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq71273
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq71273
    | exact resolve eq71273 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71273
  have eq71303 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq70227 eq71289
    | exact resolve eq71289 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71289
  have eq71319 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq71303 eq80
    | (have j0 := eq80 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq80 eq71303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq70615 eq71319
    | exact resolve eq71319 eq70615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70615 eq71319
  have eq71330 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq71320
       have r₂ := eq28
       grind)
    | exact resolve eq71320 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71320
  have eq71343 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq71330 eq52
    | exact resolve eq52 eq71330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71350 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq71330 eq13
    | exact resolve eq13 eq71330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74229 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq71343
    | (have j0 := eq71343 (σ y)
       grind)
    | exact resolve eq71343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq74348 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq71343 eq74229
    | exact resolve eq74229 eq71343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71343
  have eq74414 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq74229 eq13
    | exact resolve eq13 eq74229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74229
  have eq90739 : (σ (k x (k y y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq70227 eq1598
    | exact resolve eq1598 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq90740 : (k (σ x) (k (σ y) (σ y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq90739
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq90739
    | exact resolve eq90739 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq90739
  have eq90741 : (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq70227 eq90740
    | exact resolve eq90740 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90740
  have eq90742 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq74348 eq90741
    | exact resolve eq90741 eq74348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90741
  have eq90743 : (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq70227 eq90742
    | exact resolve eq90742 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90742
  have eq92431 : (σ (k y (k y x))) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq70227 eq1664
    | exact resolve eq1664 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664
  have eq92432 : (σ (k y (k y x))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq71303 eq92431
    | exact resolve eq92431 eq71303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92431
  have eq92433 : (σ x) = (σ (k y (k y x))) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq71330 eq92432
    | exact resolve eq92432 eq71330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92432
  have eq92434 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq92433
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq92433
    | exact resolve eq92433 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq92433
  have eq92435 : (σ x) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq70227 eq92434
    | exact resolve eq92434 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92434
  have eq92436 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq71303 eq92435
    | exact resolve eq92435 eq71303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92435
  have eq92437 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq70227 eq92436
    | exact resolve eq92436 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92436
  have eq92438 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq71330 eq92437
    | exact resolve eq92437 eq71330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71330 eq92437
  have eq92439 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq71303 eq92438
    | exact resolve eq92438 eq71303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92438
  have eq92440 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq92439
       have r₂ := eq71350
       grind)
    | exact resolve eq92439 eq71350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71350 eq92439
  have eq92444 : (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq92440 eq158
    | exact resolve eq158 eq92440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq92448 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92440 eq90743
    | exact resolve eq90743 eq92440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90743 eq92440
  have eq92461 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74348 eq92448
    | exact resolve eq92448 eq74348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74348 eq92448
  have eq92463 : (τ (σ x)) = (k y y) := by
    first
    | exact superpose eq70786 eq92444
    | exact resolve eq92444 eq70786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92444
  have eq92466 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq92461
       have r₂ := eq74414
       grind)
    | exact resolve eq92461 eq74414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74414 eq92461
  have eq92467 : x = (k y y) := by
    first
    | exact superpose eq29 eq92463
    | exact resolve eq92463 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq92463
  have eq92576 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq92467
       have i₂ := eq80 y y
       grind)
    | exact superpose eq80 eq92467
    | (have j1 := eq80 y y
       grind)
    | exact resolve eq92467 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq92806 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq92576
       grind)
    | exact superpose eq92576 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq92576
       grind)
    | exact resolve eq13 eq92576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92807 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq92576
  have eq92808 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq92806
  have eq92811 : x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq92808
       have i₂ := eq92467
       grind)
    | exact superpose eq92467 eq92808
    | exact resolve eq92808 eq92467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92467 eq92808
  have eq92813 : x = (M.op y y) := by
    first
    | (have r₁ := eq92811
       have r₂ := eq92807
       grind)
    | exact resolve eq92811 eq92807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92807 eq92811
  have eq92831 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq52 y x
       have i₂ := eq92813
       grind)
    | exact superpose eq92813 eq52
    | exact resolve eq52 eq92813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq92813
  have eq93175 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq92831 y
       grind)
    | exact superpose eq92831 eq19
    | (have j1 := eq92831 y
       grind)
    | exact resolve eq19 eq92831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq92831
  have eq93182 : y = (M.op x x) := by
    first
    | exact superpose eq70786 eq93175
    | exact resolve eq93175 eq70786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70786 eq93175
  have eq93231 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq93182
       grind)
    | exact superpose eq93182 eq98
    | exact resolve eq98 eq93182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq93182
  have eq93336 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq92466 eq93231
    | exact resolve eq93231 eq92466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93231
  have eq93345 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq93336
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq93336
    | exact resolve eq93336 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq93336
  have eq93349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq70227 eq93345
    | exact resolve eq93345 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93345
  have eq93350 : x = y := by
    first
    | (have r₁ := eq93349
       have r₂ := eq28
       grind)
    | exact resolve eq93349 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93349
  have eq93359 : (σ (k x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq93350
       grind)
    | exact superpose eq93350 eq72
    | exact resolve eq72 eq93350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq93350
  have eq93722 : (σ (k x x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq70227 eq93359
    | exact resolve eq93359 eq70227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70227 eq93359
  have eq93872 : (σ (M.op x y)) = (σ (k x x)) := by
    first
    | exact superpose eq71303 eq93722
    | exact resolve eq93722 eq71303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71303 eq93722
  have eq93961 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq93872
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq93872
    | exact resolve eq93872 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq93872
  have eq94043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92466 eq93961
    | exact resolve eq93961 eq92466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92466 eq93961
  have eq94082 : False := by grind
  exact eq94082

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pyx_x_pxx_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq56 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq67 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq72 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 X0 X0 X2 X3
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 (M.op X0 X1) x x X4
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (M.op (M.op X0 X1) X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq112 : ∀ X0 X1 X2 X3 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (M.op (σ X0) X1) X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X0 (M.op (M.op (M.op (σ X0) X1) X2) X3)
       have i₂ := eq77 (σ X0) X1 X2 X3
       grind)
    | exact superpose eq77 eq31
    | exact resolve eq31 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq113 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op (M.op (τ X0) X1) X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 (M.op (M.op (M.op (τ X0) X1) X2) X3)
       have i₂ := eq77 (τ X0) X1 X2 X3
       grind)
    | exact superpose eq77 eq18
    | exact resolve eq18 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op (M.op (M.op (τ X0) X1) X2) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq113
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : ∀ X0 X1 X2 X3 : G, (k X0 (τ (M.op (M.op (M.op (σ X0) X1) X2) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112
    | exact resolve eq112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq129 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 x X1
       have i₂ := eq74 X0 x X2
       grind)
    | (have i₁ := eq74 X0 X0 x
       have i₂ := eq74 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq74 eq74
    | exact resolve eq74 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq74 X0 X1 X5
       have i₂ := eq9 (M.op X0 X1) X2 X3 X4
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq13
    | (have r₁ := eq13 X3 (M.op (M.op X3 X1) X2)
       have r₂ := eq9 X3 X1 X2 X3
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq245 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq254 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq251 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq251
    | (have j0 := eq251 (σ X0)
       grind)
    | exact resolve eq251 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq251 (τ X0)
       grind)
    | exact superpose eq251 eq18
    | (have j1 := eq251 (τ X0)
       grind)
    | exact resolve eq18 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq261 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261
    | (have j0 := eq261 X0
       grind)
    | exact resolve eq261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq1024 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2 X3
       have i₂ := eq253 X0 X1 X2 X3
       grind)
    | exact superpose eq253 eq9
    | (have j1 := eq253 X0 X1 X2 X3
       grind)
    | exact resolve eq9 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq2094 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq340 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq340 X0 X1
       grind)
    | exact superpose eq340 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq340 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq340 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq340 X0 X0
       grind)
    | exact resolve eq13 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2110 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq340 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq2111 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2094 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094
  have eq2112 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2120 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2112 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2112
    | (have j0 := eq2112 X0 X1
       grind)
    | exact resolve eq2112 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112
  have eq2688 : ∀ X0 X1 X4 : G, (M.op X0 X4) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 (M.op X0 X1) x x X4
       have i₂ := eq1024 X0 X1 x x
       grind)
    | exact superpose eq1024 eq9
    | (have j1 := eq1024 X0 X1 x x
       grind)
    | exact resolve eq9 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2703 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) X5) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq72 X0 x x x X4 X5
       have i₂ := eq1024 X0 x x x
       grind)
    | exact superpose eq1024 eq72
    | (have j1 := eq1024 X0 x x x
       grind)
    | exact resolve eq72 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq2704 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq77 X0 x x x
       have i₂ := eq1024 X0 x x x
       grind)
    | exact superpose eq1024 eq77
    | (have j1 := eq1024 X0 x x x
       grind)
    | exact resolve eq77 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq2705 : ∀ X0 X4 X5 : G, (M.op X0 X4) = (M.op (M.op X0 X0) X5) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq132 X0 x x x X4 X5
       have i₂ := eq1024 X0 x x x
       grind)
    | exact superpose eq1024 eq132
    | (have j1 := eq1024 X0 x x x
       grind)
    | exact resolve eq132 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq2707 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0 x x x
       have i₂ := eq1024 (τ X0) x x x
       grind)
    | exact superpose eq1024 eq114
    | (have j1 := eq1024 (τ X0) x x x
       grind)
    | exact resolve eq114 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2709 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq115 X0 x x x
       have i₂ := eq1024 (σ X0) x x x
       grind)
    | exact superpose eq1024 eq115
    | (have j1 := eq1024 (σ X0) x x x
       grind)
    | exact resolve eq115 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2727 : ∀ X0 X3 X4 : G, (M.op X0 X4) = (M.op X0 X3) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq129 (M.op (M.op X0 x) x) x x
       have i₂ := eq1024 X0 x x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq1024 eq129
    | (have j1 := eq1024 X0 x x X3
       grind)
    | exact resolve eq129 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq2774 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2709 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2709
    | (have j0 := eq2709 X0
       grind)
    | exact resolve eq2709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709
  have eq2776 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2707 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2707
    | (have j0 := eq2707 X0
       grind)
    | exact resolve eq2707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq2810 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2774 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2774
    | (have j0 := eq2774 X0
       grind)
    | exact resolve eq2774 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq2812 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2776 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq2776
    | (have j0 := eq2776 X0
       grind)
    | exact resolve eq2776 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2776
  have eq2853 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704
  have eq4718 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2812 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2812
    | (have j0 := eq2812 (σ X0)
       grind)
    | exact resolve eq2812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4727 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (τ X0) X1) X2) X3) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2812 X0
       have i₂ := eq9 (τ X0) X1 X2 X3
       grind)
    | exact superpose eq9 eq2812
    | (have j0 := eq2812 X0
       grind)
    | exact resolve eq2812 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2812
  have eq4795 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4718 X0
       have i₂ := eq24 (σ X0) X0
       grind)
    | exact superpose eq24 eq4718
    | (have j0 := eq4718 X0
       grind)
    | exact resolve eq4718 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4718
  have eq4801 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4795 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4795
    | (have j0 := eq4795 X0
       grind)
    | exact resolve eq4795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4795
  have eq4803 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4801 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4801
    | (have j0 := eq4801 X0
       grind)
    | exact resolve eq4801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4801
  have eq5111 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2810 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2810
    | (have j0 := eq2810 (τ X0)
       grind)
    | exact resolve eq2810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5119 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ X0) X1) X2) X3) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2810 X0
       have i₂ := eq9 (σ X0) X1 X2 X3
       grind)
    | exact superpose eq9 eq2810
    | (have j0 := eq2810 X0
       grind)
    | exact resolve eq2810 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5125 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op (σ (k X0 X0)) X1) X2))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X0 (σ X0) X1 X2
       have i₂ := eq2810 X0
       grind)
    | exact superpose eq2810 eq115
    | (have j1 := eq2810 X0
       grind)
    | exact resolve eq115 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq5134 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) X1) = (M.op (σ (k X0 X0)) X2) ∨ (k X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 (σ X0) X1 X2
       have i₂ := eq2810 X0
       grind)
    | exact superpose eq2810 eq129
    | (have j1 := eq2810 X0
       grind)
    | exact resolve eq129 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq5186 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5111 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq5111
    | (have j0 := eq5111 X0
       grind)
    | exact resolve eq5111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5190 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5186 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5186
    | (have j0 := eq5186 X0
       grind)
    | exact resolve eq5186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186
  have eq5192 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5190 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq5190
    | (have j0 := eq5190 X0
       grind)
    | exact resolve eq5190 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5190
  have eq9748 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq254 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq9969 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9748 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq9748
    | (have j0 := eq9748 (τ X0)
       grind)
    | exact resolve eq9748 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9970 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9748 X0
       have i₂ := eq4803 X0
       grind)
    | exact superpose eq4803 eq9748
    | (have j0 := eq9748 X0
       have j1 := eq4803 X0
       grind)
    | (have r₁ := eq9748 X0
       have r₂ := eq4803 X0
       grind)
    | exact resolve eq9748 eq4803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803 eq9748
  have eq9971 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq9970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9970
  have eq9972 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9969 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9969
    | (have j0 := eq9969 X0
       grind)
    | exact resolve eq9969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9969
  have eq9975 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9972 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9972
    | (have j0 := eq9972 X0
       grind)
    | exact resolve eq9972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9972
  have eq9985 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9975 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq9975
    | (have j0 := eq9975 (τ X0)
       grind)
    | exact resolve eq9975 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10258 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (M.op (σ X0) X2) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 (σ X0) X1 X2
       have i₂ := eq9971 X0
       grind)
    | exact superpose eq9971 eq129
    | (have j1 := eq9971 X0
       grind)
    | exact resolve eq129 eq9971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10343 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9985 X0
       have i₂ := eq5192 X0
       grind)
    | exact superpose eq5192 eq9985
    | (have j0 := eq9985 X0
       have j1 := eq5192 X0
       grind)
    | (have r₁ := eq9985 X0
       have r₂ := eq5192 X0
       grind)
    | exact resolve eq9985 eq5192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5192 eq9985
  have eq10347 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10343
  have eq10491 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq262 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq262
    | exact resolve eq262 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq10550 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10491 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq10491
    | (have j0 := eq10491 X0
       grind)
    | exact resolve eq10491 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10491
  have eq10621 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10347 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10347
    | (have j0 := eq10347 (σ X0)
       grind)
    | exact resolve eq10347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10347
  have eq10730 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10621 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq10621
    | (have j0 := eq10621 X0
       grind)
    | exact resolve eq10621 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10621
  have eq13915 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9971 X0
       have i₂ := eq10258 X0 (σ X0) X1
       grind)
    | (have i₁ := eq9971 X0
       have i₂ := eq10258 X0 X1 (σ X0)
       grind)
    | exact superpose eq10258 eq9971
    | (have j0 := eq9971 X0
       have j1 := eq10258 X0 X1 x
       grind)
    | exact resolve eq9971 eq10258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9971 eq10258
  have eq13992 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13915 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13915
  have eq14067 : (σ (M.op x y)) ≠ (σ x) ∨ (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13992 x (σ y)
       grind)
    | exact superpose eq13992 eq16
    | (have j1 := eq13992 x x
       grind)
    | exact resolve eq16 eq13992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13992
  have eq14181 : ∀ X0 : G, (σ x) ≠ (σ (M.op x X0)) ∨ (k x x) = (M.op x x) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14067
       have i₂ := eq2727 x X0 y
       grind)
    | (have i₁ := eq14067
       have i₂ := eq2727 x y X0
       grind)
    | exact superpose eq2727 eq14067
    | (have j1 := eq2727 x x x
       grind)
    | exact resolve eq14067 eq2727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727 eq14067
  have eq14182 : ∀ X0 : G, (σ x) ≠ (σ (M.op x X0)) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14181
  have eq14185 : ∀ X0 : G, (σ x) ≠ (σ (M.op (M.op x x) X0)) ∨ (k x x) = (M.op x x) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14182 x
       have i₂ := eq2705 x x X0
       grind)
    | exact superpose eq2705 eq14182
    | (have j1 := eq2705 x x x
       grind)
    | exact resolve eq14182 eq2705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705 eq14182
  have eq14190 : ∀ X0 : G, (σ x) ≠ (σ (M.op (M.op x x) X0)) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14185 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14185
  have eq18794 : (σ x) ≠ (σ x) ∨ (k x x) = (M.op x x) ∨ (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq14190 x
       have i₂ := eq2703 x x x
       grind)
    | exact superpose eq2703 eq14190
    | (have j1 := eq2703 x x x
       grind)
    | exact resolve eq14190 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703 eq14190
  have eq18803 : (σ x) ≠ (σ x) ∨ (k x x) = (M.op x x) := by grind
  clear eq18794
  have eq18804 : (k x x) = (M.op x x) := by grind
  clear eq18803
  have eq32854 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (τ X0) X1) X2) X3) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq4727 X0 X1 X2 X3
       have j1 := eq9975 X0
       grind)
    | (have r₁ := eq4727 X0 X1 X2 X3
       have r₂ := eq9975 X0
       grind)
    | exact resolve eq4727 eq9975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727
  have eq45007 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (τ X0) X1) X2) X3) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32854 X0 X1 X2 X3
       have i₂ := eq251 X0
       grind)
    | exact superpose eq251 eq32854
    | (have j0 := eq32854 X0 X1 X2 X3
       have j1 := eq251 X0
       grind)
    | exact resolve eq32854 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45258 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op (M.op (τ X0) X1) X2) X3)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq32854 X0 X1 X2 X3
       grind)
    | exact superpose eq32854 eq11
    | (have j1 := eq32854 X0 X1 X2 X3
       grind)
    | exact resolve eq11 eq32854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32854
  have eq45301 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (τ X0) X1) X2) X3) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq45007 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45007
  have eq50088 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ X0) X1) X2) X3) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq5119 X0 X1 X2 X3
       have j1 := eq9975 X0
       grind)
    | (have r₁ := eq5119 X0 X1 X2 X3
       have r₂ := eq9975 X0
       grind)
    | exact resolve eq5119 eq9975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5119
  have eq50089 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op (σ (k X0 X0)) X1) X2))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq5125 X0 X1 X2
       have j1 := eq9975 X0
       grind)
    | (have r₁ := eq5125 X0 X1 X2
       have r₂ := eq9975 X0
       grind)
    | exact resolve eq5125 eq9975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5125
  have eq50091 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) X1) = (M.op (σ (k X0 X0)) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq5134 X0 X1 X2
       have j1 := eq9975 X0
       grind)
    | (have r₁ := eq5134 X0 X1 X2
       have r₂ := eq9975 X0
       grind)
    | exact resolve eq5134 eq9975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5134
  have eq59576 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (σ (M.op (M.op (M.op (τ X0) X1) X2) X3)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251 X0
       have i₂ := eq45258 X0 X1 X2 X3
       grind)
    | exact superpose eq45258 eq251
    | (have j0 := eq251 X0
       have j1 := eq45258 X0 X1 X2 X3
       grind)
    | exact resolve eq251 eq45258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59640 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op (M.op (τ X0) X1) X2) X3)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9975 X0
       have i₂ := eq45258 X0 X1 X2 X3
       grind)
    | exact superpose eq45258 eq9975
    | (have j0 := eq9975 X0
       have j1 := eq45258 X0 X1 X2 X3
       grind)
    | exact resolve eq9975 eq45258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59750 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op (M.op (τ X0) X1) X2) X3)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq59640 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59640
  have eq59766 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (σ (M.op (M.op (M.op (τ X0) X1) X2) X3)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq59576 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59576
  have eq60274 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59750 X0 x x x
       have i₂ := eq9 (τ X0) x x x
       grind)
    | exact superpose eq9 eq59750
    | (have j0 := eq59750 X0 x x x
       grind)
    | exact resolve eq59750 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59750
  have eq60405 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq60274 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60274
    | (have j0 := eq60274 (σ X0)
       grind)
    | exact resolve eq60274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60274
  have eq61414 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45301 X0 x x x
       have i₂ := eq9 (τ X0) x x x
       grind)
    | exact superpose eq9 eq45301
    | (have j0 := eq45301 X0 x x x
       grind)
    | exact resolve eq45301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45301
  have eq62159 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq61414 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61414
    | (have j0 := eq61414 (σ X0)
       grind)
    | exact resolve eq61414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62256 : ∀ X0 X1 X2 : G, (k X0 X0) = (σ (M.op (M.op (τ (M.op X0 X0)) X1) X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45258 X0 (τ X0) X1 X2
       have i₂ := eq61414 X0
       grind)
    | exact superpose eq61414 eq45258
    | (have j0 := eq45258 X0 X1 X2 x
       have j1 := eq61414 X0
       grind)
    | exact resolve eq45258 eq61414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45258 eq61414
  have eq62394 : ∀ X0 X1 X2 : G, (k X0 X0) = (σ (M.op (M.op (τ (M.op X0 X0)) X1) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq62256 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62256
  have eq64822 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ X0) X1) X2) X3) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10550 X0
       have i₂ := eq50088 X0 X1 X2 X3
       grind)
    | exact superpose eq50088 eq10550
    | (have j0 := eq10550 X0
       have j1 := eq50088 X0 X1 X2 X3
       grind)
    | exact resolve eq10550 eq50088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64834 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op (M.op (σ X0) X1) X2) X3)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq50088 X0 X1 X2 X3
       grind)
    | exact superpose eq50088 eq10
    | (have j1 := eq50088 X0 X1 X2 X3
       grind)
    | exact resolve eq10 eq50088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50088
  have eq64889 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ X0) X1) X2) X3) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq64822 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64822
  have eq65181 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op (σ (M.op X0 X0)) X1) X2))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50089 X0 X1 X2
       have i₂ := eq10550 X0
       grind)
    | exact superpose eq10550 eq50089
    | (have j0 := eq50089 X0 X1 X2
       have j1 := eq10550 X0
       grind)
    | exact resolve eq50089 eq10550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50089
  have eq65299 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op (σ (M.op X0 X0)) X1) X2))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq65181 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65181
  have eq65459 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50091 X0 X1 X2
       have i₂ := eq10550 X0
       grind)
    | exact superpose eq10550 eq50091
    | (have j0 := eq50091 X0 X1 X2
       have j1 := eq10550 X0
       grind)
    | exact resolve eq50091 eq10550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50091
  have eq65826 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq65459 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65459
  have eq83011 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59766 X0 x x x
       have i₂ := eq9 (τ X0) x x x
       grind)
    | exact superpose eq9 eq59766
    | (have j0 := eq59766 X0 x x x
       grind)
    | exact resolve eq59766 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59766
  have eq83916 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq83011 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83011
    | (have j0 := eq83011 (σ X0)
       grind)
    | exact resolve eq83011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83011
  have eq88256 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (τ (M.op (M.op (M.op (σ X0) X1) X2) X3)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251 X0
       have i₂ := eq64834 X0 X1 X2 X3
       grind)
    | exact superpose eq64834 eq251
    | (have j0 := eq251 X0
       have j1 := eq64834 X0 X1 X2 X3
       grind)
    | exact resolve eq251 eq64834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq88327 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op (M.op (σ X0) X1) X2) X3)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9975 X0
       have i₂ := eq64834 X0 X1 X2 X3
       grind)
    | exact superpose eq64834 eq9975
    | (have j0 := eq9975 X0
       have j1 := eq64834 X0 X1 X2 X3
       grind)
    | exact resolve eq9975 eq64834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9975 eq64834
  have eq88492 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op (M.op (σ X0) X1) X2) X3)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq88327 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88327
  have eq88508 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (τ (M.op (M.op (M.op (σ X0) X1) X2) X3)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq88256 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88256
  have eq89043 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (σ (k X0 X0)) X1) X2)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88492 X0 (σ X0) X1 X2
       have i₂ := eq10730 X0
       grind)
    | exact superpose eq10730 eq88492
    | (have j0 := eq88492 X0 X1 X2 x
       have j1 := eq10730 X0
       grind)
    | exact resolve eq88492 eq10730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10730 eq88492
  have eq89192 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (σ (k X0 X0)) X1) X2)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq89043 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89043
  have eq90480 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (σ (M.op X0 X0)) X1) X2)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89192 X0 X1 X2
       have i₂ := eq10550 X0
       grind)
    | exact superpose eq10550 eq89192
    | (have j0 := eq89192 X0 X1 X2
       have j1 := eq10550 X0
       grind)
    | exact resolve eq89192 eq10550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10550 eq89192
  have eq90577 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (σ (M.op X0 X0)) X1) X2)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq90480 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90480
  have eq91481 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64889 X0 x x x
       have i₂ := eq9 (σ X0) x x x
       grind)
    | exact superpose eq9 eq64889
    | (have j0 := eq64889 X0 x x x
       grind)
    | exact resolve eq64889 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64889
  have eq119767 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq88508 X0 x x x
       have i₂ := eq9 (σ X0) x x x
       grind)
    | exact superpose eq9 eq88508
    | (have j0 := eq88508 X0 x x x
       grind)
    | exact resolve eq88508 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88508
  have eq129533 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2853 (σ X0)
       have i₂ := eq83916 X0
       grind)
    | exact superpose eq83916 eq2853
    | (have j0 := eq2853 (σ X0)
       have j1 := eq83916 X0
       grind)
    | (have r₁ := eq2853 (σ X0)
       have r₂ := eq83916 X0
       grind)
    | exact resolve eq2853 eq83916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83916
  have eq129746 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq129533 X0
       have j1 := eq2853 (σ X0)
       grind)
    | (have r₁ := eq129533 X0
       have r₂ := eq2853 (σ X0)
       grind)
    | exact resolve eq129533 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129533
  have eq129802 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq129746 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq129746
    | (have j0 := eq129746 X0
       grind)
    | exact resolve eq129746 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129746
  have eq153979 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2120 X0 X1
       have j1 := eq2110 X1 X0
       grind)
    | (have r₁ := eq2120 X1 X0
       have r₂ := eq2110 X0 X1
       grind)
    | (have r₁ := eq2120 X1 (k X1 X0)
       have r₂ := eq2110 X0 X1
       grind)
    | (have r₁ := eq2120 X1 X1
       have r₂ := eq2110 X1 X1
       grind)
    | exact resolve eq2120 eq2110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110 eq2120
  have eq154074 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq153979 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq153979
    | exact resolve eq153979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154148 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq153979 y x
       grind)
    | exact superpose eq153979 eq16
    | (have j1 := eq153979 y x
       grind)
    | exact resolve eq16 eq153979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153979
  have eq154529 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq154074 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq154074
    | (have j0 := eq154074 X0 X1
       grind)
    | exact resolve eq154074 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq154074
  have eq154643 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154529 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq154529
    | exact resolve eq154529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154728 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq154529 X1 X0
       grind)
    | exact superpose eq154529 eq24
    | (have j1 := eq154529 X1 X0
       grind)
    | exact resolve eq24 eq154529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq154529
  have eq155705 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154728 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq154728
    | exact resolve eq154728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154728
  have eq155975 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq155705 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq155705
    | (have j0 := eq155705 X0 X1
       grind)
    | exact resolve eq155705 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq155705
  have eq157051 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq154148
       have i₂ := eq154643 x y
       grind)
    | exact superpose eq154643 eq154148
    | (have j1 := eq154643 (σ x) (σ y)
       grind)
    | exact resolve eq154148 eq154643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154148
  have eq157056 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq157051
  have eq157082 : y = (k y (τ (σ x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67 y
       have i₂ := eq157056
       grind)
    | exact superpose eq157056 eq67
    | exact resolve eq67 eq157056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq157098 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq62159 y
       have i₂ := eq157056
       grind)
    | exact superpose eq157056 eq62159
    | exact resolve eq62159 eq157056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62159
  have eq157105 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq119767 y
       have i₂ := eq157056
       grind)
    | exact superpose eq157056 eq119767
    | (have j0 := eq119767 y
       grind)
    | exact resolve eq119767 eq157056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157056
  have eq157402 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq157105
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq157105
    | exact resolve eq157105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157105
  have eq157403 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq157402
  have eq157406 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq157098
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq157098
    | exact resolve eq157098 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157098
  have eq157407 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq157406
  have eq157411 : y = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq157082
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq157082
    | exact resolve eq157082 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157082
  have eq157482 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq154643 x y
       have i₂ := eq157411
       grind)
    | exact superpose eq157411 eq154643
    | (have j0 := eq154643 x y
       grind)
    | exact resolve eq154643 eq157411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154643 eq157411
  have eq157485 : y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq157482
  have eq157498 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op y X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x y X0 X1
       have i₂ := eq157485
       grind)
    | exact superpose eq157485 eq9
    | exact resolve eq9 eq157485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157485
  have eq157897 : ∀ X0 X1 : G, y = (M.op (M.op y X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y y x x
       have i₂ := eq157403
       grind)
    | exact superpose eq157403 eq9
    | exact resolve eq9 eq157403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157992 : x ≠ y ∨ x = (M.op y y) := by grind
  have eq164365 : ∀ X0 : G, (M.op x x) = (M.op y X0) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq157498 y x
       have i₂ := eq157403
       grind)
    | exact superpose eq157403 eq157498
    | exact resolve eq157498 eq157403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157403
  have eq164429 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq157897 x x
       have i₂ := eq157498 x x
       grind)
    | exact superpose eq157498 eq157897
    | exact resolve eq157897 eq157498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157498 eq157897
  have eq164710 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq164429
  have eq164860 : ∀ X0 : G, (M.op x x) = (M.op y X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq164365 X0
       grind)
    | (have r₁ := eq164365 X0
       have r₂ := eq157992
       grind)
    | exact resolve eq164365 eq157992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157992 eq164365
  have eq164964 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq129802 x
       have i₂ := eq164710
       grind)
    | exact superpose eq164710 eq129802
    | (have j0 := eq129802 x
       grind)
    | exact resolve eq129802 eq164710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129802 eq164710
  have eq165145 : (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq164964
       have r₂ := eq157407
       grind)
    | exact resolve eq164964 eq157407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157407 eq164964
  have eq165196 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq165145
       have i₂ := eq18804
       grind)
    | exact superpose eq18804 eq165145
    | exact resolve eq165145 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165145
  have eq165403 : x ≠ (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq164860
  have eq168577 : (M.op x x) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq165196
       grind)
    | exact superpose eq165196 eq10
    | exact resolve eq10 eq165196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165196
  have eq168696 : x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq168577
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq168577
    | exact resolve eq168577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168577
  have eq168705 : x = (M.op y y) := by
    first
    | (have r₁ := eq168696
       have r₂ := eq165403
       grind)
    | exact resolve eq168696 eq165403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165403 eq168696
  have eq168717 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op y X1) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 y X1 X0
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq74
    | exact resolve eq74 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168720 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq129 y X1 x
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq129
    | exact resolve eq129 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq168744 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq60405 y
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq60405
    | (have j0 := eq60405 y
       grind)
    | exact resolve eq60405 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60405
  have eq168749 : ∀ X0 X1 : G, y = (k y (τ (M.op (M.op (σ x) X0) X1))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq65299 y X1 x
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq65299
    | exact resolve eq65299 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65299
  have eq168750 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq65826 y X1 x
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq65826
    | exact resolve eq65826 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65826
  have eq168755 : ∀ X0 X1 : G, y ≠ (τ (M.op (M.op (σ x) X0) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq90577 y X1 x
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq90577
    | exact resolve eq90577 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90577
  have eq168762 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y y x x
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq9
    | exact resolve eq9 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182676 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq168750 (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq168750 X0 (σ y)
       grind)
    | exact superpose eq168750 eq16
    | exact resolve eq16 eq168750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168750
  have eq191537 : ∀ X0 X1 : G, (M.op (σ x) X1) ≠ (σ (M.op x X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq182676 X1
       have i₂ := eq168720 y X0
       grind)
    | (have i₁ := eq182676 X1
       have i₂ := eq168720 X0 y
       grind)
    | exact superpose eq168720 eq182676
    | exact resolve eq182676 eq168720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168720 eq182676
  have eq208208 : ∀ X0 : G, y = (k y (τ (M.op (σ x) X0))) ∨ x = y ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq168749 x (M.op (σ x) x)
       have i₂ := eq2688 (σ x) x X0
       grind)
    | exact superpose eq2688 eq168749
    | (have j1 := eq2688 (σ x) x x
       grind)
    | exact resolve eq168749 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688 eq168749
  have eq208263 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (k x x)) ∨ y = (k y (τ (M.op (σ x) X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq208208 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq208208
    | (have j0 := eq208208 X0
       grind)
    | exact resolve eq208208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208208
  have eq208305 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ y = (k y (τ (M.op (σ x) X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq208263 X0
       have i₂ := eq18804
       grind)
    | exact superpose eq18804 eq208263
    | (have j0 := eq208263 X0
       grind)
    | exact resolve eq208263 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208263
  have eq208330 : ∀ X0 : G, y = (k y (τ (M.op (σ x) X0))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq208305 X0
       grind)
    | (have r₁ := eq208305 X0
       have r₂ := eq191537 x (σ x)
       grind)
    | exact resolve eq208305 eq191537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208305
  have eq208403 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 (M.op (σ x) X0) y
       have i₂ := eq208330 X0
       grind)
    | exact superpose eq208330 eq19
    | exact resolve eq19 eq208330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq208330
  have eq208853 : ∀ X0 : G, (τ (σ y)) = (τ (M.op (M.op (σ x) X0) (σ y))) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq155975 (M.op (σ x) X0) (σ y)
       have i₂ := eq208403 X0
       grind)
    | exact superpose eq208403 eq155975
    | (have j0 := eq155975 (M.op (σ x) X0) (σ y)
       grind)
    | exact resolve eq155975 eq208403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155975 eq208403
  have eq208859 : ∀ X0 : G, y = (τ (M.op (M.op (σ x) X0) (σ y))) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq208853 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq208853
    | (have j0 := eq208853 X0
       grind)
    | exact resolve eq208853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208853
  have eq208886 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq208859 X0
       grind)
    | (have r₁ := eq208859 X0
       have r₂ := eq168755 X0 (σ y)
       grind)
    | exact resolve eq208859 eq168755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168755 eq208859
  have eq208985 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq91481 y
       have i₂ := eq208886 X0
       grind)
    | exact superpose eq208886 eq91481
    | (have j0 := eq91481 y
       grind)
    | exact resolve eq91481 eq208886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91481
  have eq208987 : ∀ X0 : G, (M.op y y) = (τ (M.op (σ x) X0)) ∨ y = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq119767 y
       have i₂ := eq208886 X0
       grind)
    | exact superpose eq208886 eq119767
    | (have j0 := eq119767 y
       grind)
    | exact resolve eq119767 eq208886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119767 eq208886
  have eq209644 : ∀ X0 : G, x = (τ (M.op (σ x) X0)) ∨ y = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq208987 X0
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq208987
    | exact resolve eq208987 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208987
  have eq209645 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq208985 X0
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq208985
    | exact resolve eq208985 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208985
  have eq209830 : ∀ X0 : G, x = y ∨ x = (τ (M.op (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq209644 X0
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq209644
    | (have j0 := eq209644 X0
       grind)
    | exact resolve eq209644 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209644
  have eq209831 : ∀ X0 : G, x = (τ (M.op (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq209830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209830
  have eq209832 : ∀ X0 : G, x = y ∨ (σ x) = (M.op (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq209645 X0
       have i₂ := eq168705
       grind)
    | exact superpose eq168705 eq209645
    | (have j0 := eq209645 X0
       grind)
    | exact resolve eq209645 eq168705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168705 eq209645
  have eq209833 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq209832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209832
  have eq211543 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (σ (M.op (M.op x X0) X1)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq62394 (σ x) X0 X1
       have i₂ := eq209831 (σ x)
       grind)
    | exact superpose eq209831 eq62394
    | (have j0 := eq62394 (σ x) X1 x
       grind)
    | exact resolve eq62394 eq209831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62394 eq209831
  have eq211649 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq211543 x x
       have i₂ := eq168762 x x
       grind)
    | exact superpose eq168762 eq211543
    | exact resolve eq211543 eq168762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211543
  have eq211681 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have j1 := eq2853 (σ x)
       grind)
    | (have r₁ := eq211649
       have r₂ := eq2853 (σ x)
       grind)
    | exact resolve eq211649 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2853 eq211649
  have eq211698 : (σ x) = (σ (k x x)) ∨ x = y := by
    first
    | (have i₁ := eq211681
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq211681
    | exact resolve eq211681 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211681
  have eq211706 : (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq211698
       have i₂ := eq18804
       grind)
    | exact superpose eq18804 eq211698
    | exact resolve eq211698 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18804 eq211698
  have eq213833 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq191537 x X0
       have i₂ := eq211706
       grind)
    | exact superpose eq211706 eq191537
    | exact resolve eq191537 eq211706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191537 eq211706
  have eq213936 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq213833 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213833
  have eq213985 : x = y := by
    first
    | (have r₁ := eq213936 x
       have r₂ := eq209833 x
       grind)
    | exact resolve eq213936 eq209833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209833 eq213936
  have eq214027 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq168717 X0 X1
       have i₂ := eq213985
       grind)
    | exact superpose eq213985 eq168717
    | exact resolve eq168717 eq213985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168717
  have eq214035 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq168744
       have i₂ := eq213985
       grind)
    | exact superpose eq213985 eq168744
    | exact resolve eq168744 eq213985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168744 eq213985
  have eq214060 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq214035
  have eq214075 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq214027 X0 x
       have i₂ := eq168762 x (M.op x x)
       grind)
    | exact superpose eq168762 eq214027
    | exact resolve eq214027 eq168762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168762 eq214027
  have eq218753 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq74 (σ x) (σ x) x
       have i₂ := eq214060
       grind)
    | exact superpose eq214060 eq74
    | exact resolve eq74 eq214060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq218933 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq218753 X0
       have i₂ := eq214060
       grind)
    | exact superpose eq214060 eq218753
    | exact resolve eq218753 eq214060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214060 eq218753
  have eq219184 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq218933 (σ y)
       grind)
    | exact superpose eq218933 eq16
    | exact resolve eq16 eq218933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218933
  have eq219561 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq219184
       have i₂ := eq214075 y
       grind)
    | exact superpose eq214075 eq219184
    | exact resolve eq219184 eq214075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214075 eq219184
  have eq219562 : False := by grind
  exact eq219562

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then Y else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_y_pyx_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq64 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
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
  have eq440 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq467 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq440
    | (have j0 := eq440 X0 X1
       grind)
    | exact resolve eq440 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq470 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq437
    | (have j0 := eq437 X0 X1
       grind)
    | exact resolve eq437 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq471 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq436
    | (have j0 := eq436 X0 X1
       grind)
    | exact resolve eq436 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq501 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq467
    | (have j0 := eq467 X0 X1
       grind)
    | exact resolve eq467 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq504 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq470
    | (have j0 := eq470 X0 X1
       grind)
    | exact resolve eq470 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq505 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq471
    | (have j0 := eq471 X0 X1
       grind)
    | exact resolve eq471 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq871 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq504
    | exact resolve eq504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq901 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq871 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq871
    | (have j0 := eq871 X0 X1
       grind)
    | exact resolve eq871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq923 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq901 X1 X0
       grind)
    | exact superpose eq901 eq10
    | (have j1 := eq901 X1 X0
       grind)
    | exact resolve eq10 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq923 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq923
    | (have j0 := eq923 X0 X1
       grind)
    | exact resolve eq923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq968 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq958 X0 X1
       grind)
    | exact superpose eq958 eq92
    | (have j0 := eq92 X0 X1
       have j1 := eq958 X0 X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq958 X0 X1
       grind)
    | (have r₁ := eq92 X1 X1
       have r₂ := eq958 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq958 X0 (M.op X0 X1)
       grind)
    | exact resolve eq92 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq993 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq968 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1037 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq993 (σ X0) X1
       grind)
    | exact superpose eq993 eq29
    | (have j1 := eq993 (σ X0) X1
       grind)
    | exact resolve eq29 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq993
  have eq2633 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq505 (σ x) y
       grind)
    | exact superpose eq505 eq16
    | (have j1 := eq505 (σ y) x
       grind)
    | (have r₁ := eq16
       have r₂ := eq505 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq2642 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2633
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2633
    | exact resolve eq2633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq4108 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq1037 X1 (σ X0)
       grind)
    | exact superpose eq1037 eq23
    | (have j1 := eq1037 X1 (σ X0)
       grind)
    | exact resolve eq23 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1037
  have eq4149 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4108 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4108
    | (have j0 := eq4108 X0 X1
       grind)
    | exact resolve eq4108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4183 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4149 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4149
    | (have j0 := eq4149 X0 X1
       grind)
    | exact resolve eq4149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq4192 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4183 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4183
    | (have j0 := eq4183 X0 X1
       grind)
    | exact resolve eq4183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183
  have eq5121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4192 X1 X0
       grind)
    | exact superpose eq4192 eq11
    | (have j1 := eq4192 X1 X0
       grind)
    | exact resolve eq11 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192
  have eq5787 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5121 x y
       grind)
    | exact superpose eq5121 eq16
    | (have j1 := eq5121 x y
       grind)
    | exact resolve eq16 eq5121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5121
  have eq5845 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5787
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5787
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq5787 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5787
  have eq5851 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq5845
  have eq5854 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5851
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq5851
    | exact resolve eq5851 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5851
  have eq5855 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5854
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq5854
    | exact resolve eq5854 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5854
  have eq5872 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5855
       grind)
    | exact superpose eq5855 eq16
    | exact resolve eq16 eq5855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5855
  have eq5873 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5872
       have i₂ := eq64 (σ x)
       grind)
    | exact superpose eq64 eq5872
    | exact resolve eq5872 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5872
  have eq5874 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5873
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq5873
    | exact resolve eq5873 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873
  have eq5875 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq5874
  have eq5879 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67 x y
       have i₂ := eq5875
       grind)
    | exact superpose eq5875 eq67
    | exact resolve eq67 eq5875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5893 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq5913 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5879
       have i₂ := eq5875
       grind)
    | exact superpose eq5875 eq5879
    | exact resolve eq5879 eq5875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5875 eq5879
  have eq5930 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq5913
  have eq5934 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5930
       have r₂ := eq5893
       grind)
    | exact resolve eq5930 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5893 eq5930
  have eq18694 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2642
       have i₂ := eq5934
       grind)
    | exact superpose eq5934 eq2642
    | exact resolve eq2642 eq5934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642 eq5934
  have eq18716 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq18694
  have eq18717 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq18716
  have eq18725 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18717
       grind)
    | exact superpose eq18717 eq10
    | exact resolve eq10 eq18717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18717
  have eq18782 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18725
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18725
    | exact resolve eq18725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18725
  have eq18784 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18782
       grind)
    | exact superpose eq18782 eq16
    | exact resolve eq16 eq18782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18782
  have eq18787 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18784
       have i₂ := eq64 (σ x)
       grind)
    | exact superpose eq64 eq18784
    | exact resolve eq18784 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18784
  have eq18789 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18787
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq18787
    | exact resolve eq18787 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18787
  have eq18790 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq18789
  have eq18815 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq18790
       grind)
    | exact superpose eq18790 eq11
    | exact resolve eq11 eq18790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18790
  have eq18931 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18815
       grind)
    | exact superpose eq18815 eq16
    | exact resolve eq16 eq18815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18942 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq67 (σ x) (σ y)
       have i₂ := eq18815
       grind)
    | exact superpose eq18815 eq67
    | exact resolve eq67 eq18815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq19043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18931
       have i₂ := eq901 y x
       grind)
    | exact superpose eq901 eq18931
    | (have j1 := eq901 y x
       grind)
    | (have r₁ := eq18931
       have r₂ := eq901 y x
       grind)
    | (have r₁ := eq18931
       have r₂ := eq901 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq18931
       have r₂ := eq901 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq18931 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq19044 : x = y ∨ x = (M.op x y) := by grind
  clear eq19043
  have eq19055 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18931
       have i₂ := eq19044
       grind)
    | exact superpose eq19044 eq18931
    | exact resolve eq18931 eq19044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19044
  have eq19056 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19055
       have i₂ := eq97 x
       grind)
    | exact superpose eq97 eq19055
    | exact resolve eq19055 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq19055
  have eq19061 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19056
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq19056
    | exact resolve eq19056 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq19056
  have eq19062 : x = (M.op x y) := by grind
  clear eq19061
  have eq19082 : x ≠ x ∨ y = (k x y) := by
    first
    | (have i₁ := eq92 x y
       have i₂ := eq19062
       grind)
    | exact superpose eq19062 eq92
    | (have j0 := eq92 x y
       grind)
    | (have r₁ := eq92 x y
       have r₂ := eq19062
       grind)
    | exact resolve eq92 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq19103 : y = (k x y) := by grind
  clear eq19082
  have eq19119 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq18931
       have i₂ := eq19103
       grind)
    | exact superpose eq19103 eq18931
    | exact resolve eq18931 eq19103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18931
  have eq19135 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq19119
       have i₂ := eq19062
       grind)
    | exact superpose eq19062 eq19119
    | exact resolve eq19119 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19062 eq19119
  have eq19437 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq18942
       have i₂ := eq501 x (k x y)
       grind)
    | exact superpose eq501 eq18942
    | (have j1 := eq501 x (k x y)
       grind)
    | exact resolve eq18942 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq18942
  have eq19499 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq19437
       have i₂ := eq19103
       grind)
    | exact superpose eq19103 eq19437
    | exact resolve eq19437 eq19103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19437
  have eq19500 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq19499
  have eq19514 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq19500
       have i₂ := eq19103
       grind)
    | exact superpose eq19103 eq19500
    | exact resolve eq19500 eq19103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19500
  have eq19525 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq19514
       have i₂ := eq18815
       grind)
    | exact superpose eq18815 eq19514
    | exact resolve eq19514 eq18815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18815 eq19514
  have eq19526 : (σ x) = (σ (k x y)) := by grind
  clear eq19525
  have eq19532 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19526
       have i₂ := eq19103
       grind)
    | exact superpose eq19103 eq19526
    | exact resolve eq19526 eq19103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19103 eq19526
  have eq19536 : False := by grind
  exact eq19536

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pyx_pxx_y_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq95
    | exact resolve eq95 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq95
  have eq248 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq16
    | (have r₁ := eq16
       have r₂ := eq106 x y
       grind)
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq256 : False := by grind
  exact eq256

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pxx_pyy_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
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
  clear eq35
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq10
    | exact resolve eq10 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq43
    | exact resolve eq43 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq69 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by
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
  have eq88 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq63 sF3
       grind)
    | exact superpose eq63 eq97
    | exact resolve eq97 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq63 y
       grind)
    | exact superpose eq63 eq101
    | exact resolve eq101 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq101
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq96
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq727 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq728 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq727
    | (have j0 := eq727 X0 X1
       grind)
    | exact resolve eq727 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq727
  have eq853 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq728 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq728 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq20834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20834
    | exact resolve eq20834 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20834
  have eq20846 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq20835
       have r₂ := eq27
       grind)
    | exact resolve eq20835 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20835
  have eq20850 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20846
    | exact resolve eq20846 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20846
  have eq20852 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20850
    | exact resolve eq20850 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20850
  have eq20868 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20852 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20852
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20852
       grind)
    | exact resolve eq13 eq20852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20852
  have eq21860 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20868
    | (have j0 := eq20868 (σ x)
       grind)
    | (have r₁ := eq20868 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq20868 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20868
  have eq21864 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21860
  have eq21873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21864 eq114
    | exact resolve eq114 eq21864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21864
  have eq21886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq21873
  have eq21888 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq21886
       have r₂ := eq27
       grind)
    | exact resolve eq21886 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21886
  have eq21891 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21888 eq88
    | (have r₁ := eq88
       have r₂ := eq21888
       grind)
    | exact resolve eq88 eq21888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21888
  have eq21925 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq21891
  have eq22909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21925 eq114
    | exact resolve eq114 eq21925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21925
  have eq22922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq22909
  have eq22924 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq22922
       have r₂ := eq27
       grind)
    | exact resolve eq22922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22922
  have eq22941 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq22924 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22924
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22924
       grind)
    | exact resolve eq13 eq22924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22924
  have eq23947 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq22941
    | (have j0 := eq22941 (σ x)
       grind)
    | (have r₁ := eq22941 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq22941 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22941
  have eq23954 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq23947
  have eq24047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq23954 eq114
    | exact resolve eq114 eq23954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq23954
  have eq24060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq24047
  have eq24062 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq24060
       have r₂ := eq27
       grind)
    | exact resolve eq24060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24060
  have eq24066 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq24062
       grind)
    | exact superpose eq24062 eq103
    | exact resolve eq103 eq24062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24081 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq24062
       grind)
    | exact superpose eq24062 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq24062
       grind)
    | exact resolve eq13 eq24062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24062
  have eq24118 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq24066
    | exact resolve eq24066 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24066
  have eq25363 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24081 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24081
    | (have j0 := eq24081 x
       grind)
    | (have r₁ := eq24081 x
       have r₂ := eq18
       grind)
    | exact resolve eq24081 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24081
  have eq25371 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq25363
  have eq25378 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq25371
       grind)
    | exact superpose eq25371 eq96
    | exact resolve eq96 eq25371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25391 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq854 x y
       have i₂ := eq25371
       grind)
    | exact superpose eq25371 eq854
    | (have j0 := eq854 x y
       grind)
    | exact resolve eq854 eq25371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq25371
  have eq25395 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25391
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq25391
    | exact resolve eq25391 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25391
  have eq25408 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq25378
    | exact resolve eq25378 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25378
  have eq25410 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq25395
    | exact resolve eq25395 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25395
  have eq25417 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq25410
       have r₂ := eq24118
       grind)
    | exact resolve eq25410 eq24118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25410
  have eq25422 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25417
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq25417
    | exact resolve eq25417 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25417
  have eq25427 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25422
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25422
    | exact resolve eq25422 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25422
  have eq25432 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25427
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25427
    | exact resolve eq25427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25427
  have eq25437 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq25432
    | exact resolve eq25432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25432
  have eq25442 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25437
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq25437
    | exact resolve eq25437 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25437
  have eq25447 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25442
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25442
    | exact resolve eq25442 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25442
  have eq25452 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25447
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25447
    | exact resolve eq25447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25447
  have eq25456 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq25452
    | exact resolve eq25452 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25452
  have eq27620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq25456 eq24118
    | exact resolve eq24118 eq25456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25456
  have eq27659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq27620
  have eq27666 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq27659
       have r₂ := eq27
       grind)
    | exact resolve eq27659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27659
  have eq27948 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27666 eq88
    | (have r₁ := eq88
       have r₂ := eq27666
       grind)
    | exact resolve eq88 eq27666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq27666
  have eq27986 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq27948
  have eq30647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27986 eq25408
    | exact resolve eq25408 eq27986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25408 eq27986
  have eq30658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq30647
  have eq30668 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq30658
       have r₂ := eq27
       grind)
    | exact resolve eq30658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30658
  have eq30688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq30668 eq24118
    | exact resolve eq24118 eq30668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24118 eq30668
  have eq30727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq30688
  have eq30734 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq30727
       have r₂ := eq27
       grind)
    | exact resolve eq30727 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30727
  have eq30738 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq30734
       grind)
    | exact superpose eq30734 eq69
    | exact resolve eq69 eq30734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30739 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq30734
       grind)
    | exact superpose eq30734 eq87
    | (have r₁ := eq87
       have r₂ := eq30734
       grind)
    | exact resolve eq87 eq30734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq30734
  have eq30775 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq30739
  have eq30788 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq30738
    | exact resolve eq30738 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30738
  have eq32554 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq30775
       grind)
    | exact superpose eq30775 eq96
    | exact resolve eq96 eq30775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq32570 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq853 x y
       have i₂ := eq30775
       grind)
    | exact superpose eq30775 eq853
    | (have j0 := eq853 x y
       grind)
    | exact resolve eq853 eq30775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30775
  have eq32572 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32570
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq32570
    | exact resolve eq32570 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32570
  have eq32586 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq32554
    | exact resolve eq32554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32554
  have eq32587 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq30788 eq32572
    | (have r₁ := eq32572
       have r₂ := eq30788
       grind)
    | exact resolve eq32572 eq30788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32572
  have eq32594 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq32587
       have r₂ := eq20
       grind)
    | exact resolve eq32587 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32587
  have eq32599 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32594
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq32594
    | exact resolve eq32594 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32594
  have eq32604 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq30788 eq32599
    | exact resolve eq32599 eq30788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32599
  have eq32609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32604
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32604
    | exact resolve eq32604 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32604
  have eq32614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32609
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32609
    | exact resolve eq32609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32609
  have eq32619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq32614
    | exact resolve eq32614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32614
  have eq32624 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq32619
       have r₂ := eq27
       grind)
    | exact resolve eq32619 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32619
  have eq32629 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32624
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq32624
    | exact resolve eq32624 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32624
  have eq32634 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32629
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32629
    | exact resolve eq32629 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32629
  have eq32639 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32634
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32634
    | exact resolve eq32634 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32634
  have eq32644 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq32639
    | exact resolve eq32639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32639
  have eq33078 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq32644 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq32644
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq32644
       grind)
    | exact resolve eq13 eq32644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32644
  have eq42336 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq33078
    | (have j0 := eq33078 (σ x)
       grind)
    | (have r₁ := eq33078 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq33078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33078
  have eq42351 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42336
  have eq42381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq42351 eq32586
    | exact resolve eq32586 eq42351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32586 eq42351
  have eq42392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42381
  have eq42405 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq42392
       have r₂ := eq27
       grind)
    | exact resolve eq42392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42392
  have eq42411 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq42405
       grind)
    | exact superpose eq42405 eq103
    | exact resolve eq103 eq42405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42429 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq42405
       grind)
    | exact superpose eq42405 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq42405
       grind)
    | exact resolve eq13 eq42405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42405
  have eq42467 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq42411
    | exact resolve eq42411 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42411
  have eq44100 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq42429 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42429
    | (have j0 := eq42429 x
       grind)
    | (have r₁ := eq42429 x
       have r₂ := eq18
       grind)
    | exact resolve eq42429 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq42429
  have eq44108 : (M.op x y) = (k y x) := by grind
  clear eq44100
  have eq44494 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq853 x y
       have i₂ := eq44108
       grind)
    | exact superpose eq44108 eq853
    | (have j0 := eq853 x y
       grind)
    | exact resolve eq853 eq44108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq44108
  have eq44496 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq44494
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq44494
    | exact resolve eq44494 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44494
  have eq44511 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq30788 eq44496
    | (have r₁ := eq44496
       have r₂ := eq30788
       grind)
    | exact resolve eq44496 eq30788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44496
  have eq44518 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq44511
       have r₂ := eq20
       grind)
    | exact resolve eq44511 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq44511
  have eq44523 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq44518
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq44518
    | exact resolve eq44518 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq44518
  have eq44528 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq30788 eq44523
    | exact resolve eq44523 eq30788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30788 eq44523
  have eq44533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq44528
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44528
    | exact resolve eq44528 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44528
  have eq44538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq44533
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44533
    | exact resolve eq44533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44533
  have eq44543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq44538
    | exact resolve eq44538 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44538
  have eq44548 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq44543
       have r₂ := eq27
       grind)
    | exact resolve eq44543 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44543
  have eq44553 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq44548
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq44548
    | exact resolve eq44548 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq44548
  have eq44558 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq42467 eq44553
    | exact resolve eq44553 eq42467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42467 eq44553
  have eq44563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44558
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44558
    | exact resolve eq44558 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq44558
  have eq44568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44563
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44563
    | exact resolve eq44563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq44563
  have eq44573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq44568
    | exact resolve eq44568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq44568
  have eq44578 : False := by grind
  exact eq44578
