import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq9 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq120 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq120 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq120 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq120 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq122
    | exact resolve eq122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq122
    | exact resolve eq122 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq125 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq124
    | exact resolve eq124 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq126 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq123 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq123
    | exact resolve eq123 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq123
  have eq161 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X2 X1
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq168 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X3) (M.op X3 X2)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 X2
       have i₂ := eq168 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq168 X1 X1
       grind)
    | exact superpose eq168 eq9
    | (have j1 := eq168 X0 X1
       grind)
    | exact resolve eq9 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X2) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq775 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op X0 X3) ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq630 x X0 X3 (M.op x x)
       have i₂ := eq262 X0 X3 x x
       grind)
    | exact superpose eq262 eq630
    | (have j1 := eq262 X0 X3 x X3
       grind)
    | exact resolve eq630 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq887 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq775 X0 X1
       grind)
    | (have i₁ := eq168 X0 X0
       have i₂ := eq775 X0 x
       grind)
    | exact superpose eq775 eq168
    | (have j0 := eq168 X0 X1
       have j1 := eq775 X0 X1
       grind)
    | exact resolve eq168 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq888 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq262 X0 X1 X3 X2
       have i₂ := eq775 X0 X1
       grind)
    | (have i₁ := eq262 X0 X0 X2 X3
       have i₂ := eq775 X0 X3
       grind)
    | exact superpose eq775 eq262
    | (have j0 := eq262 X0 X1 X2 X3
       have j1 := eq775 X0 X1
       grind)
    | exact resolve eq262 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq775
  have eq912 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq888 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq913 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq918 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq912 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq912
    | (have j0 := eq912 X0 X1 x x
       grind)
    | exact resolve eq912 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq1019 : ∀ X0 X1 X2 X3 : G, (τ X1) = (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X2 X3)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq161 X1 X3 X2
       have i₂ := eq913 X0 X1
       grind)
    | (have i₁ := eq161 X0 X1 X2
       have i₂ := eq913 X0 X1
       grind)
    | exact superpose eq913 eq161
    | (have j1 := eq913 X0 X1
       grind)
    | exact resolve eq161 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq1066 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1 x x
       have i₂ := eq161 X0 x x
       grind)
    | exact superpose eq161 eq1019
    | (have j0 := eq1019 X0 X1 x x
       grind)
    | exact resolve eq1019 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq1019
  have eq1084 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1066
    | (have j0 := eq1066 (σ X0) (σ X1)
       grind)
    | exact resolve eq1066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1109 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1084 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1084
    | (have j0 := eq1084 X0 X1
       grind)
    | exact resolve eq1084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1109 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1109
    | (have j0 := eq1109 X0 X1
       grind)
    | exact resolve eq1109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1255 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1114 y x
       grind)
    | exact superpose eq1114 eq16
    | (have j1 := eq1114 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1114 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1114 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1277 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1255
       have i₂ := eq918 y x
       grind)
    | exact superpose eq918 eq1255
    | (have j1 := eq918 x y
       grind)
    | (have r₁ := eq1255
       have r₂ := eq918 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1255
       have r₂ := eq918 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1255 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq1255
  have eq1282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq1277
  have eq1283 : x = y := by grind
  clear eq1282
  have eq1288 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1283
       grind)
    | exact superpose eq1283 eq16
    | exact resolve eq16 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1289 : False := by grind
  exact eq1289

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pyx_pxy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq9 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq120 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq120 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq120 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq120 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq122
    | exact resolve eq122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq122
    | exact resolve eq122 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq125 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq124
    | exact resolve eq124 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq126 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq123 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq123
    | exact resolve eq123 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq123
  have eq161 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X2 X1
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq168 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X3) (M.op X3 X2)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 X2
       have i₂ := eq168 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq168 X1 X1
       grind)
    | exact superpose eq168 eq9
    | (have j1 := eq168 X0 X1
       grind)
    | exact resolve eq9 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X2) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq815 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op X0 X3) ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq611 x X0 X3 (M.op x x)
       have i₂ := eq262 X0 X3 x x
       grind)
    | exact superpose eq262 eq611
    | (have j1 := eq262 X0 X3 x X3
       grind)
    | exact resolve eq611 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq926 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq815 X0 X1
       grind)
    | (have i₁ := eq168 X0 X0
       have i₂ := eq815 X0 x
       grind)
    | exact superpose eq815 eq168
    | (have j0 := eq168 X0 X1
       have j1 := eq815 X0 X1
       grind)
    | exact resolve eq168 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq927 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq262 X0 X1 X3 X2
       have i₂ := eq815 X0 X1
       grind)
    | (have i₁ := eq262 X0 X0 X2 X3
       have i₂ := eq815 X0 X3
       grind)
    | exact superpose eq815 eq262
    | (have j0 := eq262 X0 X1 X2 X3
       have j1 := eq815 X0 X1
       grind)
    | exact resolve eq262 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq815
  have eq955 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq927 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq956 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq926 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq961 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq955
    | (have j0 := eq955 X0 X1 x x
       grind)
    | exact resolve eq955 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1264 : ∀ X0 X1 X2 X3 : G, (τ X1) = (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X2 X3)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq161 X1 X3 X2
       have i₂ := eq956 X0 X1
       grind)
    | (have i₁ := eq161 X0 X1 X2
       have i₂ := eq956 X0 X1
       grind)
    | exact superpose eq956 eq161
    | (have j1 := eq956 X0 X1
       grind)
    | exact resolve eq161 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1317 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X0 X1 x x
       have i₂ := eq161 X0 x x
       grind)
    | exact superpose eq161 eq1264
    | (have j0 := eq1264 X0 X1 x x
       grind)
    | exact resolve eq1264 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq1264
  have eq1336 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1317 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1317
    | (have j0 := eq1317 (σ X0) (σ X1)
       grind)
    | exact resolve eq1317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1361 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1336 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1336
    | (have j0 := eq1336 X0 X1
       grind)
    | exact resolve eq1336 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1366 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1361 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1361
    | (have j0 := eq1361 X0 X1
       grind)
    | exact resolve eq1361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1408 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1366 y x
       grind)
    | exact superpose eq1366 eq16
    | (have j1 := eq1366 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1366 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1366 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq1432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1408
       have i₂ := eq961 y x
       grind)
    | exact superpose eq961 eq1408
    | (have j1 := eq961 x y
       grind)
    | (have r₁ := eq1408
       have r₂ := eq961 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1408
       have r₂ := eq961 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1408 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq1408
  have eq1437 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq1432
  have eq1438 : x = y := by grind
  clear eq1437
  have eq1568 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1438
       grind)
    | exact superpose eq1438 eq16
    | exact resolve eq16 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1569 : False := by grind
  exact eq1569

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pyy_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (k X0 X1) (M.op X1 X1)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq178 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (σ y) = (M.op (M.op (k (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq179
    | exact resolve eq179 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq183 : ∀ X0 : G, y = (M.op (M.op (k y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq175 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (k (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq189
    | exact resolve eq189 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq650 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq188 (M.op (k X0 X0) X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq188
    | exact resolve eq188 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq192
  have eq660 : (M.op (k x x) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq650 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq650
    | (have j0 := eq650 x y
       grind)
    | exact resolve eq650 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : (M.op (k (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq650
    | (have j0 := eq650 (σ x) (σ y)
       grind)
    | exact resolve eq650 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq187 x x X0
       have i₂ := eq660
       grind)
    | exact superpose eq660 eq187
    | exact resolve eq187 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq690 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq661 eq187
    | exact resolve eq187 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq661
  have eq780 : (M.op x y) = (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
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
  have eq781 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq780
       grind)
    | exact superpose eq780 eq41
    | exact resolve eq41 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq780
  have eq1244 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1243
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1243
    | exact resolve eq1243 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1246 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq1244
    | exact resolve eq1244 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1246 eq781
    | exact resolve eq781 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq1246
  have eq1290 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1283
       have r₂ := eq27
       grind)
    | exact resolve eq1283 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1295 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1290 eq690
    | exact resolve eq690 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq1302 : (M.op (k (σ y) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1290 eq650
    | exact resolve eq650 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1316 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq650 sF4 sF2
       grind)
    | exact superpose eq650 eq1295
    | exact resolve eq1295 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq2191 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1302 eq182
    | exact resolve eq182 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1302
  have eq2222 : (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2191
       have i₂ := eq650 sF4 sF3
       grind)
    | exact superpose eq650 eq2191
    | exact resolve eq2191 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq2229 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1316 eq2222
    | exact resolve eq2222 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq2222
  have eq2230 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2229
  have eq2236 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq684 y
       have i₂ := eq2230
       grind)
    | exact superpose eq2230 eq684
    | exact resolve eq684 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq2243 : (M.op (k y y) y) = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq650 y x
       have i₂ := eq2230
       grind)
    | exact superpose eq2230 eq650
    | exact resolve eq650 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2259 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2236
       have i₂ := eq650 sF0 x
       grind)
    | exact superpose eq650 eq2236
    | exact resolve eq2236 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq4161 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq2243
       grind)
    | exact superpose eq2243 eq183
    | exact resolve eq183 eq2243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq2243
  have eq4202 : y = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4161
       have i₂ := eq650 sF0 y
       grind)
    | exact superpose eq650 eq4161
    | exact resolve eq4161 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq4161
  have eq4212 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2259 eq4202
    | exact resolve eq4202 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259 eq4202
  have eq4213 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4212
  have eq4220 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4213 eq32
    | exact resolve eq32 eq4213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4213
  have eq4272 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq4220
    | exact resolve eq4220 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4220
  have eq4273 : x = y := by grind
  clear eq4272
  have eq4276 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4273
       grind)
    | exact superpose eq4273 eq18
    | exact resolve eq18 eq4273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4277 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4273
       grind)
    | exact superpose eq4273 eq24
    | exact resolve eq24 eq4273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4273
  have eq4300 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4277
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4277
    | exact resolve eq4277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277
  have eq4301 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq4276
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq4276
    | exact resolve eq4276 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4276
  have eq4302 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4300 eq26
    | exact resolve eq26 eq4300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4300
  have eq4346 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4302
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq4302
    | exact resolve eq4302 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq4302
  have eq4352 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4301
       grind)
    | exact superpose eq4301 eq40
    | exact resolve eq40 eq4301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4301
  have eq4363 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4352
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4352
    | exact resolve eq4352 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4352
  have eq4366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4346 eq4363
    | exact resolve eq4363 eq4346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4346 eq4363
  have eq4368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4366
    | exact resolve eq4366 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4366
  have eq4370 : False := by grind
  exact eq4370

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxy_pxx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq64 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq64 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq64 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq208 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq213 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq208 X0 X1
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq208 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq208 X1 X0
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq208 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq208
  have eq312 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq213 (σ X0) (σ X1)
       grind)
    | exact superpose eq213 eq15
    | exact resolve eq15 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq213 X0 X1
       grind)
    | exact superpose eq213 eq312
    | exact resolve eq312 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq312
  have eq318 : False := by grind
  exact eq318

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq532 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq94 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq94 X0 X0
       grind)
    | exact resolve eq12 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq545 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq550 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq545 X0 X1
       have j1 := eq81 X1 (σ X0)
       grind)
    | (have r₁ := eq545 X0 X0
       have r₂ := eq81 X0 (σ X0)
       grind)
    | exact resolve eq545 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq551 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       have j1 := eq81 X1 (σ X0)
       grind)
    | (have r₁ := eq532 X0 X0
       have r₂ := eq81 X0 (σ X0)
       grind)
    | exact resolve eq532 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq532
  have eq565 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq550
    | (have j0 := eq550 X0 X1
       grind)
    | exact resolve eq550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq566 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq565 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq567 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq551
    | (have j0 := eq551 X0 X1
       grind)
    | exact resolve eq551 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq575 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq566
    | (have j0 := eq566 X0 X1
       grind)
    | exact resolve eq566 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq566
  have eq576 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq567
    | (have j0 := eq567 X0 X1
       grind)
    | exact resolve eq567 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq577 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq576 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq583 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       have j1 := eq575 X0 X1
       grind)
    | (have r₁ := eq577 X0 X1
       have r₂ := eq575 X0 X1
       grind)
    | exact resolve eq577 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq577
  have eq585 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq583 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq583
    | exact resolve eq583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq583 x y
       grind)
    | exact superpose eq583 eq16
    | exact resolve eq16 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq699 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq585 X0 (τ X1)
       grind)
    | exact superpose eq585 eq18
    | exact resolve eq18 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq585
  have eq716 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq699
    | exact resolve eq699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq724 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq716
    | exact resolve eq716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq736 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq596
       have i₂ := eq724 x y
       grind)
    | exact superpose eq724 eq596
    | exact resolve eq596 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq724
  have eq737 : False := by grind
  exact eq737

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxy_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) ∨ (k X1 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2)
       have i₂ := eq53 X1 X0 X2
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 X2
       have i₂ := eq72 X0 X1
       grind)
    | (have i₁ := eq72 X1 X1
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq72
    | exact resolve eq72 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq72 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 (M.op X0 X1)
       have i₂ := eq72 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq53 X0 X1 (M.op X1 X0)
       have i₂ := eq72 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq72 eq53
    | exact resolve eq53 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op (M.op X0 X0) X1) X3) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq80 (M.op (M.op X0 X0) X1) (M.op x X0) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq80
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq185 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq185
    | (have j0 := eq185 (σ X0) (σ X1)
       grind)
    | exact resolve eq185 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq185 (τ X0) X1
       grind)
    | exact superpose eq185 eq17
    | (have j1 := eq185 (τ X0) X1
       grind)
    | exact resolve eq17 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq185 X0 (τ X1)
       grind)
    | exact superpose eq185 eq18
    | (have j1 := eq185 X0 (τ X1)
       grind)
    | exact resolve eq18 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq193 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq185 X0 (σ X1)
       grind)
    | exact superpose eq185 eq22
    | (have j1 := eq185 X0 (σ X1)
       grind)
    | exact resolve eq22 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op X3 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) X1) (M.op x X0) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) X0) X0 X1
       have i₂ := eq51 X0 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq482 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq16
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) X1) (M.op X2 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq186 X0 X0
       grind)
    | exact superpose eq186 eq9
    | (have j1 := eq186 X0 X0
       grind)
    | exact resolve eq9 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (M.op (σ X1) (σ X1)) X2) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq9
    | (have j1 := eq186 X0 X1
       grind)
    | exact resolve eq9 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) (σ X1)
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq72
    | (have j1 := eq186 X0 X1
       grind)
    | exact resolve eq72 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (M.op X0 X0) X1 (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq84
    | exact resolve eq84 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq540 (M.op X0 X1) (M.op (M.op X0 X0) X0)
       have i₂ := eq51 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq51 eq540
    | exact resolve eq540 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq540
  have eq732 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq700 X0 X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq700
    | exact resolve eq700 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq745 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq732 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)
       have i₂ := eq732 X0 X1
       grind)
    | exact superpose eq732 eq732
    | exact resolve eq732 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X0 X0) X0) X2
       have i₂ := eq732 X0 X1
       grind)
    | exact superpose eq732 eq9
    | exact resolve eq9 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 X1
       have i₂ := eq9 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq745
    | exact resolve eq745 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq793 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq192
    | exact resolve eq192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq822 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq793 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq793
    | (have j0 := eq793 X0 X1
       grind)
    | exact resolve eq793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq837 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (M.op X2 (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq761 (σ X0) (σ X1) X2
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq761
    | (have j1 := eq186 X0 X1
       grind)
    | exact resolve eq761 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq997 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 X1)
       have i₂ := eq822 X1 X0
       grind)
    | exact superpose eq822 eq22
    | (have j1 := eq822 X1 X0
       grind)
    | exact resolve eq22 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (k (τ X2) (M.op X0 X1)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq997 X0 X1 X2
       have i₂ := eq22 X2 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq997
    | (have j0 := eq997 X0 X1 X2
       grind)
    | exact resolve eq997 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq997
  have eq1050 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (M.op X0 X1) X2
       have i₂ := eq784 X0 X1
       grind)
    | (have i₁ := eq72 (M.op X1 X1) X1
       have i₂ := eq784 X1 X1
       grind)
    | exact superpose eq784 eq72
    | exact resolve eq72 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq482
       have i₂ := eq185 x y
       grind)
    | exact superpose eq185 eq482
    | (have j1 := eq185 (σ x) (σ y)
       grind)
    | exact resolve eq482 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq1117 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1114
  have eq1121 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1117
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1117
       grind)
    | exact resolve eq13 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq80 (σ y) (σ x) X0
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq80
    | exact resolve eq80 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq83 (σ y) (σ x) X0
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq83
    | exact resolve eq83 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1139 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1122
  have eq1140 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1139
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1139
    | exact resolve eq1139 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1141 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1121
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1121
    | exact resolve eq1121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1279 : (k (τ (σ y)) x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq193 (σ y) x
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq193
    | (have j0 := eq193 (σ y) x
       grind)
    | exact resolve eq193 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq1117
  have eq1304 : x = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1279
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1279
    | exact resolve eq1279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1307 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1304
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1304
    | exact resolve eq1304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1593 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq343 X0 X1
       have i₂ := eq72 X0 X1
       grind)
    | (have i₁ := eq343 X1 X1
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq343
    | exact resolve eq343 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq1973 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (k (τ X0) (τ X0))) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq486 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq486
    | exact resolve eq486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq2054 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 (σ (τ X0))) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1973 X0 X1 X2
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1973
    | (have j0 := eq1973 X0 X1 X2
       grind)
    | exact resolve eq1973 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1973
  have eq2065 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2054 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2054
    | (have j0 := eq2054 X0 X1 X2
       grind)
    | exact resolve eq2054 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq2125 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op X0 (M.op (k X0 X0) X1)) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (k X0 X0) X1 (M.op x X0)
       have i₂ := eq2065 X0 X1 x
       grind)
    | exact superpose eq2065 eq84
    | (have j1 := eq2065 X0 X1 x
       grind)
    | exact resolve eq84 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq2065
  have eq2195 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (M.op (σ (τ X1)) (σ (τ X1))) X2) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq487 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq487
    | (have j0 := eq487 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq487 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq2247 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (M.op (σ (τ X1)) (σ (τ X1))) X2) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2195 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2195
    | (have j0 := eq2195 X0 X1 X2
       grind)
    | exact resolve eq2195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2254 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2247 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2247
    | (have j0 := eq2247 X0 X1 X2
       grind)
    | exact resolve eq2247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2255 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op (M.op (M.op X1 X1) X2) (k X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2254 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2254
    | (have j0 := eq2254 X0 X1 X2
       grind)
    | exact resolve eq2254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254
  have eq2256 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2255 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2255
    | (have j0 := eq2255 X0 X1 X2
       grind)
    | exact resolve eq2255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255
  have eq2277 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (k X2 (M.op X0 X1))) ∨ (M.op (M.op X0 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2256 X2 (M.op X0 X1) (M.op (M.op X0 X0) X0)
       have i₂ := eq732 X0 X1
       grind)
    | exact superpose eq732 eq2256
    | (have j0 := eq2256 X2 (M.op X0 X1) X2
       grind)
    | exact resolve eq2256 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2303 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op (M.op (M.op (k X1 X0) X2) (k X1 X0)) X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 (k X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq2256 X1 X0 x
       grind)
    | exact superpose eq2256 eq83
    | (have j1 := eq2256 X1 X0 X2
       grind)
    | exact resolve eq83 eq2256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq2919 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X1 X2)) ∨ (M.op X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1010 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1010
    | (have j0 := eq1010 X1 X2 X2
       grind)
    | exact resolve eq1010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq2967 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op X0 (k X1 X2)) ∨ (M.op X2 X1) = X1 ∨ (M.op (k X1 X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2919 X0 X1 X2
       have i₂ := eq185 X0 (k X1 X2)
       grind)
    | exact superpose eq185 eq2919
    | (have j0 := eq2919 X0 X1 X2
       have j1 := eq185 X1 X2
       grind)
    | exact resolve eq2919 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq3601 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1128 (σ x)
       have i₂ := eq1307
       grind)
    | exact superpose eq1307 eq1128
    | exact resolve eq1128 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq1307
  have eq3631 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (k y x) := by grind
  clear eq3601
  have eq4639 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1125 (σ y)
       have i₂ := eq3631
       grind)
    | exact superpose eq3631 eq1125
    | exact resolve eq1125 eq3631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq4685 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (k y x) := by grind
  clear eq4639
  have eq5322 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) ∨ (k X1 (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))) = (M.op X1 (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 X1 (M.op X0 X1)
       have i₂ := eq72 (M.op X0 X1) X1
       grind)
    | (have i₁ := eq75 X0 X1 (M.op X0 X1)
       have i₂ := eq72 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq72 eq75
    | exact resolve eq75 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq5879 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1))))) = (σ (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1))) ∨ (τ X0) = (M.op (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq190 X0 (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1)))
       have i₂ := eq318 (τ X0) X1 X2
       grind)
    | exact superpose eq318 eq190
    | (have j0 := eq190 X0 (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1)))
       grind)
    | exact resolve eq190 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq318
  have eq13419 : (M.op (σ x) (σ y)) = (M.op (σ (k x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1125 (σ y)
       have i₂ := eq1140
       grind)
    | exact superpose eq1140 eq1125
    | exact resolve eq1125 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq13494 : (M.op (σ x) (σ y)) = (M.op (σ (k x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq13419
  have eq13527 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (M.op X0 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2125 X0 (M.op X0 X1)
       have i₂ := eq761 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq761 eq2125
    | (have j0 := eq2125 X0 X1
       grind)
    | exact resolve eq2125 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq18867 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2303 X0 X0 (M.op X0 X1)
       have i₂ := eq13527 X0 X1
       grind)
    | exact superpose eq13527 eq2303
    | (have j0 := eq2303 X0 X0 x
       have j1 := eq13527 X0 X1
       grind)
    | exact resolve eq2303 eq13527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303 eq13527
  have eq18930 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq18867 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18867
  have eq27582 : ∀ X0 X1 : G, (M.op (M.op (σ (τ X0)) (σ (τ X0))) (σ (τ X0))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq492 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq492
    | (have j0 := eq492 (τ X0) (τ X1)
       grind)
    | exact resolve eq492 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq492
  have eq27892 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27582 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27582
    | (have j0 := eq27582 X0 X1
       grind)
    | exact resolve eq27582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27582
  have eq27914 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27892 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27892
    | (have j0 := eq27892 X0 X1
       grind)
    | exact resolve eq27892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27892
  have eq27930 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27914 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27914
    | (have j0 := eq27914 X0 X1
       grind)
    | exact resolve eq27914 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27914
  have eq27939 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27930 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27930
    | (have j0 := eq27930 X0 X1
       grind)
    | exact resolve eq27930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27930
  have eq27985 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (k X0 X2) X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27939 X0 X2
       have i₂ := eq72 X0 X1
       grind)
    | (have i₁ := eq27939 X1 X1
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq27939
    | (have j0 := eq27939 X0 X2
       grind)
    | exact resolve eq27939 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27939
  have eq68118 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2)) ∨ (k X2 (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2))) = (M.op X2 (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5322 X0 X1 X0
       have i₂ := eq80 X0 X1 X2
       grind)
    | (have i₁ := eq5322 X0 X2 X0
       have i₂ := eq80 X0 X1 X2
       grind)
    | exact superpose eq80 eq5322
    | exact resolve eq5322 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322
  have eq84363 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1140
       have i₂ := eq4685
       grind)
    | exact superpose eq4685 eq1140
    | exact resolve eq1140 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4685
  have eq84533 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (k y x) := by grind
  clear eq84363
  have eq84556 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq84533
       have r₂ := eq1141
       grind)
    | exact resolve eq84533 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84533
  have eq84565 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84556
       grind)
    | exact superpose eq84556 eq16
    | exact resolve eq16 eq84556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84556
  have eq84685 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq822 y x
       grind)
    | (have r₁ := eq84565
       have r₂ := eq822 y x
       grind)
    | exact resolve eq84565 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84565
  have eq84692 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq185 y x
       have i₂ := eq84685
       grind)
    | exact superpose eq84685 eq185
    | (have j0 := eq185 x y
       grind)
    | exact resolve eq185 eq84685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq84685
  have eq84758 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq84692
  have eq84836 : ∀ X0 : G, y = (M.op x (M.op X0 y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq761 x y x
       have i₂ := eq84758
       grind)
    | exact superpose eq84758 eq761
    | exact resolve eq761 eq84758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84848 : ∀ X0 : G, y = (M.op x (k X0 y)) ∨ (M.op y X0) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2277 x y x
       have i₂ := eq84758
       grind)
    | exact superpose eq84758 eq2277
    | exact resolve eq2277 eq84758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq85082 : ∀ X1 : G, (M.op y x) = (M.op (k x X1) x) ∨ x = (M.op X1 x) ∨ x = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq27985 x (M.op x y) X1
       have i₂ := eq84836 x
       grind)
    | exact superpose eq84836 eq27985
    | (have j0 := eq27985 x X1 X1
       grind)
    | exact resolve eq27985 eq84836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27985 eq84836
  have eq271092 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))) = (k X0 (σ (M.op X2 (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))))) ∨ (τ X0) = (M.op (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5879 X0 X1 X2
       have i₂ := eq100 (τ X0) X1 (M.op (M.op (τ X0) (τ X0)) X1)
       grind)
    | exact superpose eq100 eq5879
    | (have j0 := eq5879 X0 X1 X2
       grind)
    | exact resolve eq5879 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq271093 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))) = (k X0 (σ (M.op X2 (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))))) ∨ (τ X0) = (M.op (M.op X2 (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq271092 X0 X1 X2
       have i₂ := eq100 (τ X0) X1 (M.op (M.op (τ X0) (τ X0)) X1)
       grind)
    | exact superpose eq100 eq271092
    | (have j0 := eq271092 X0 X1 X2
       grind)
    | exact resolve eq271092 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq271092
  have eq271470 : ∀ X0 X1 X2 : G, (k X0 (τ (σ (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))))) = (τ (σ (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))) ∨ (τ (σ X0)) = (M.op (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (σ (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))))
       have i₂ := eq271093 (σ X0) X1 X2
       grind)
    | exact superpose eq271093 eq28
    | (have j1 := eq271093 (σ X0) X1 X2
       grind)
    | exact resolve eq28 eq271093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq271093
  have eq271747 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)) = (k X0 (τ (σ (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))))) ∨ (τ (σ X0)) = (M.op (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq271470 X0 X1 X2
       have i₂ := eq10 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))
       grind)
    | exact superpose eq10 eq271470
    | (have j0 := eq271470 X0 X1 X2
       grind)
    | exact resolve eq271470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271470
  have eq271914 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)) = (k X0 (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))) ∨ (τ (σ X0)) = (M.op (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq271747 X0 X1 X2
       have i₂ := eq10 (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))
       grind)
    | exact superpose eq10 eq271747
    | (have j0 := eq271747 X0 X1 X2
       grind)
    | exact resolve eq271747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271747
  have eq272036 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (k X0 (M.op X2 (M.op X0 (M.op (M.op X0 X0) X1)))) ∨ (τ (σ X0)) = (M.op (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq271914 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq271914
    | (have j0 := eq271914 X0 X1 X2
       grind)
    | exact resolve eq271914 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271914
  have eq272086 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (k X0 (M.op X2 (M.op X0 (M.op (M.op X0 X0) X1)))) ∨ (M.op (M.op X2 (M.op X0 (M.op (M.op X0 X0) X1))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq272036 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq272036
    | (have j0 := eq272036 X0 X1 X2
       grind)
    | exact resolve eq272036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272036
  have eq422540 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X0) (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))) (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18930 (M.op (M.op X0 X1) X0) (M.op x X0)
       have i₂ := eq83 X0 X1 x
       grind)
    | exact superpose eq83 eq18930
    | (have j0 := eq18930 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact resolve eq18930 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18930
  have eq423974 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq422540 X0 X1
       have i₂ := eq9 X0 (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq422540
    | (have j0 := eq422540 X0 X1
       grind)
    | exact resolve eq422540 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422540
  have eq424230 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq423974 X0 X1
       have i₂ := eq83 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq423974
    | (have j0 := eq423974 X0 X1
       grind)
    | exact resolve eq423974 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423974
  have eq1344956 : ∀ X0 : G, (k X0 y) = (M.op X0 (k x y)) ∨ x = (M.op y x) ∨ (M.op (k x y) X0) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2967 X0 x y
       have i₂ := eq84758
       grind)
    | exact superpose eq84758 eq2967
    | (have j0 := eq2967 X0 x y
       grind)
    | exact resolve eq2967 eq84758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967 eq84758
  have eq1345984 : ∀ X0 : G, (k X0 y) = (M.op X0 (k x y)) ∨ x = (M.op y x) ∨ (M.op (k x y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1344956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344956
  have eq1347391 : y = (k x y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op (k x y) x) := by
    first
    | (have i₁ := eq84848 x
       have i₂ := eq1345984 x
       grind)
    | exact superpose eq1345984 eq84848
    | (have j0 := eq84848 x
       have j1 := eq1345984 x
       grind)
    | exact resolve eq84848 eq1345984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84848 eq1345984
  have eq1347612 : x = (M.op (k x y) x) ∨ x = (M.op y x) ∨ y = (k x y) := by grind
  clear eq1347391
  have eq1347933 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq85082 y
       have i₂ := eq1347612
       grind)
    | exact superpose eq1347612 eq85082
    | (have j0 := eq85082 y
       grind)
    | exact resolve eq85082 eq1347612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85082 eq1347612
  have eq1348212 : y = (k x y) ∨ x = (M.op y x) := by grind
  clear eq1347933
  have eq1348227 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13494
       have i₂ := eq1348212
       grind)
    | exact superpose eq1348212 eq13494
    | exact resolve eq13494 eq1348212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13494 eq1348212
  have eq1348575 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1348227
  have eq2541631 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X2 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq272086 X0 (M.op X0 X1) X2
       have i₂ := eq761 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq761 eq272086
    | exact resolve eq272086 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272086
  have eq2673043 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1140
       have i₂ := eq1348575
       grind)
    | exact superpose eq1348575 eq1140
    | exact resolve eq1140 eq1348575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq1348575
  have eq2673541 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq2673043
  have eq2673654 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2673541
       have r₂ := eq1141
       grind)
    | exact resolve eq2673541 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq2673541
  have eq2673681 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2673654
       grind)
    | exact superpose eq2673654 eq16
    | exact resolve eq16 eq2673654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673654
  have eq2674024 : x = (M.op y x) := by
    first
    | (have j1 := eq822 y x
       grind)
    | (have r₁ := eq2673681
       have r₂ := eq822 y x
       grind)
    | exact resolve eq2673681 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq2673681
  have eq2674102 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq2674024
       grind)
    | exact superpose eq2674024 eq9
    | exact resolve eq9 eq2674024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2674108 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq80 y x X0
       have i₂ := eq2674024
       grind)
    | exact superpose eq2674024 eq80
    | exact resolve eq80 eq2674024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2674111 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq83 y x X0
       have i₂ := eq2674024
       grind)
    | exact superpose eq2674024 eq83
    | exact resolve eq83 eq2674024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2674137 : ∀ X0 : G, x = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq761 y x x
       have i₂ := eq2674024
       grind)
    | exact superpose eq2674024 eq761
    | exact resolve eq761 eq2674024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq2674285 : ∀ X0 : G, y = (M.op (M.op X0 x) y) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq2541631 y x x
       have i₂ := eq2674024
       grind)
    | exact superpose eq2674024 eq2541631
    | exact resolve eq2541631 eq2674024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541631
  have eq2722829 : y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2674285 (M.op (M.op x x) x)
       have i₂ := eq2674102 x
       grind)
    | exact superpose eq2674102 eq2674285
    | exact resolve eq2674285 eq2674102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674102
  have eq2723335 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) y) ∨ x = (k y (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq1593 y x x
       have i₂ := eq2674285 y
       grind)
    | exact superpose eq2674285 eq1593
    | (have j1 := eq2674285 y
       grind)
    | exact resolve eq1593 eq2674285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq2723579 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ (M.op y (M.op X0 x)) = (k y (M.op X0 x)) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq12 y (M.op X0 x)
       have i₂ := eq2674285 X0
       grind)
    | exact superpose eq2674285 eq12
    | (have j0 := eq12 y (M.op X0 x)
       have j1 := eq2674285 X0
       grind)
    | exact resolve eq12 eq2674285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674285
  have eq2723888 : ∀ X0 : G, x = (k y (M.op X0 x)) ∨ y ≠ (M.op X0 x) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq2723579 X0
       have i₂ := eq2674137 X0
       grind)
    | exact superpose eq2674137 eq2723579
    | (have j0 := eq2723579 X0
       grind)
    | exact resolve eq2723579 eq2674137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674137 eq2723579
  have eq2723889 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have j0 := eq2723888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723888
  have eq2724000 : (M.op x y) = (M.op y y) ∨ x = (k y (M.op y x)) := by
    first
    | (have i₁ := eq2723335 x
       have i₂ := eq2674108 x
       grind)
    | exact superpose eq2674108 eq2723335
    | exact resolve eq2723335 eq2674108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674108 eq2723335
  have eq2724134 : (M.op x y) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2724000
       have i₂ := eq2674024
       grind)
    | exact superpose eq2674024 eq2724000
    | exact resolve eq2724000 eq2674024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724000
  have eq2724514 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq2722829
       grind)
    | exact superpose eq2722829 eq9
    | exact resolve eq9 eq2722829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2724522 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) x) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq80 x X0 y
       have i₂ := eq2722829
       grind)
    | exact superpose eq2722829 eq80
    | exact resolve eq80 eq2722829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq2722829
  have eq2724822 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq2724522 X0
       have i₂ := eq2674024
       grind)
    | exact superpose eq2674024 eq2724522
    | exact resolve eq2724522 eq2674024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674024 eq2724522
  have eq2745661 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ x = (k y x) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq2724514 X0
       have i₂ := eq2724134
       grind)
    | exact superpose eq2724134 eq2724514
    | exact resolve eq2724514 eq2724134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724134 eq2724514
  have eq2746104 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq2745661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745661
  have eq2773645 : y = (M.op (M.op (M.op x x) x) y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2746104 x
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq2746104
    | exact resolve eq2746104 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2746104
  have eq2781370 : y ≠ y ∨ y = (M.op (M.op x x) x) ∨ (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) = (k y (M.op (M.op x x) x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y (M.op (M.op x x) x)
       have i₂ := eq2773645
       grind)
    | exact superpose eq2773645 eq13
    | (have j0 := eq13 y (M.op (M.op x x) x)
       grind)
    | (have r₁ := eq13 y (M.op (M.op x x) x)
       have r₂ := eq2773645
       grind)
    | exact resolve eq13 eq2773645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773645
  have eq2781552 : y = (M.op (M.op x x) x) ∨ (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) = (k y (M.op (M.op x x) x)) ∨ x = (k y x) := by grind
  clear eq2781370
  have eq2781708 : x = (k y (M.op (M.op x x) x)) ∨ y = (M.op (M.op x x) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2781552
       have i₂ := eq9 x x (M.op x x)
       grind)
    | exact superpose eq9 eq2781552
    | exact resolve eq2781552 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781552
  have eq2781822 : x = (k y (M.op (M.op x x) x)) ∨ x = (k y x) := by
    first
    | (have j1 := eq2723889 (M.op x x)
       grind)
    | (have r₁ := eq2781708
       have r₂ := eq2723889 (M.op x x)
       grind)
    | exact resolve eq2781708 eq2723889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723889 eq2781708
  have eq2782637 : x = (k y x) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2781822
       have i₂ := eq2724822 x
       grind)
    | exact superpose eq2724822 eq2781822
    | exact resolve eq2781822 eq2724822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724822 eq2781822
  have eq2782833 : x = (k y x) := by grind
  clear eq2782637
  have eq2783002 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq837 y x x
       have i₂ := eq2782833
       grind)
    | exact superpose eq2782833 eq837
    | (have j0 := eq837 y x x
       grind)
    | exact resolve eq837 eq2782833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq3327683 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) (M.op (M.op X0 X1) (M.op X0 X1))) X0) ≠ X0 ∨ (k (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) (M.op (M.op X0 X1) (M.op X0 X1))) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) (M.op (M.op X0 X1) (M.op X0 X1))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68118 (M.op (M.op X0 X1) (M.op X0 X1)) X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq732 X0 X1
       grind)
    | exact superpose eq732 eq68118
    | exact resolve eq68118 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq68118
  have eq3328917 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ X0 ∨ (k (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) (M.op (M.op X0 X1) (M.op X0 X1))) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) (M.op (M.op X0 X1) (M.op X0 X1))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3327683 X0 X1 X2
       have i₂ := eq9 (M.op X0 X1) X2 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq3327683
    | (have j0 := eq3327683 X0 X1 X2
       grind)
    | exact resolve eq3327683 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327683
  have eq3329851 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) (M.op (M.op X0 X1) (M.op X0 X1))) X0)) = X0 ∨ (M.op (M.op X0 X1) X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3328917 X0 X1 X2
       have i₂ := eq9 X0 X0 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) (M.op (M.op X0 X1) (M.op X0 X1)))
       grind)
    | exact superpose eq9 eq3328917
    | (have j0 := eq3328917 X0 X1 X2
       grind)
    | exact resolve eq3328917 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328917
  have eq3330639 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X0 ∨ (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3329851 X0 X1 x
       have i₂ := eq9 (M.op X0 X1) x (M.op X0 X1)
       grind)
    | exact superpose eq9 eq3329851
    | (have j0 := eq3329851 X0 X1 x
       grind)
    | exact resolve eq3329851 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3329851
  have eq3356093 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3330639 (M.op X0 X1) x
       have i₂ := eq1050 X0 X1 x
       grind)
    | (have i₁ := eq3330639 (M.op X1 X1) (M.op X1 X1)
       have i₂ := eq1050 X1 X1 x
       grind)
    | exact superpose eq1050 eq3330639
    | (have j0 := eq3330639 (M.op X0 X0) X1
       grind)
    | exact resolve eq3330639 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050 eq3330639
  have eq3356349 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3356093 X0 X1
       have j1 := eq424230 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq3356093 X0 X1
       have r₂ := eq424230 (M.op X0 X0) X1
       grind)
    | exact resolve eq3356093 eq424230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424230 eq3356093
  have eq3357019 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3356349 x x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq3356349
    | exact resolve eq3356349 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356349
  have eq3359455 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3357019 (σ X0)
       grind)
    | exact superpose eq3357019 eq15
    | exact resolve eq15 eq3357019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3360906 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3359455 X0
       have i₂ := eq3357019 X0
       grind)
    | exact superpose eq3357019 eq3359455
    | exact resolve eq3359455 eq3357019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357019 eq3359455
  have eq3364919 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq3360906 X0
       grind)
    | exact superpose eq3360906 eq9
    | exact resolve eq9 eq3360906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3385276 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3364919 (M.op x y) x
       have i₂ := eq2674111 x
       grind)
    | exact superpose eq2674111 eq3364919
    | exact resolve eq3364919 eq2674111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674111
  have eq3386927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3385276 (M.op x (σ x))
       have i₂ := eq2783002 x
       grind)
    | exact superpose eq2783002 eq3385276
    | exact resolve eq3385276 eq2783002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783002
  have eq3387869 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3386927
       have r₂ := eq16
       grind)
    | exact resolve eq3386927 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386927
  have eq3388196 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3387869
       grind)
    | exact superpose eq3387869 eq16
    | exact resolve eq16 eq3387869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3388297 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3387869
       grind)
    | exact superpose eq3387869 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3387869
       grind)
    | exact resolve eq13 eq3387869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3388332 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq784 (σ x) (σ y)
       have i₂ := eq3387869
       grind)
    | exact superpose eq3387869 eq784
    | exact resolve eq784 eq3387869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq3388531 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by grind
  clear eq3388297
  have eq3388640 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq3388332
       have i₂ := eq3360906 x
       grind)
    | exact superpose eq3360906 eq3388332
    | exact resolve eq3388332 eq3360906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388332
  have eq3388657 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3388531
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3388531
    | exact resolve eq3388531 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388531
  have eq3388778 : (σ (M.op y y)) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq3388640
       have i₂ := eq3360906 y
       grind)
    | exact superpose eq3360906 eq3388640
    | exact resolve eq3388640 eq3360906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388640
  have eq3388788 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3388657
       have i₂ := eq3360906 x
       grind)
    | exact superpose eq3360906 eq3388657
    | exact resolve eq3388657 eq3360906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388657
  have eq3388878 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3388788
       have i₂ := eq2782833
       grind)
    | exact superpose eq2782833 eq3388788
    | exact resolve eq3388788 eq2782833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782833 eq3388788
  have eq3406688 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3388778
       have i₂ := eq3388878
       grind)
    | exact superpose eq3388878 eq3388778
    | exact resolve eq3388778 eq3388878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388778 eq3388878
  have eq3408072 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3406688
       have i₂ := eq3387869
       grind)
    | exact superpose eq3387869 eq3406688
    | exact resolve eq3406688 eq3387869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387869 eq3406688
  have eq3418361 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3364919 y x
       have i₂ := eq3408072
       grind)
    | exact superpose eq3408072 eq3364919
    | exact resolve eq3364919 eq3408072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364919 eq3408072
  have eq3419730 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3418361 x
       have i₂ := eq3385276 x
       grind)
    | exact superpose eq3385276 eq3418361
    | exact resolve eq3418361 eq3385276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385276 eq3418361
  have eq3419844 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3419730
       have r₂ := eq3388196
       grind)
    | exact resolve eq3419730 eq3388196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388196 eq3419730
  have eq3419994 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3419844
       grind)
    | exact superpose eq3419844 eq10
    | exact resolve eq10 eq3419844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419844
  have eq3421313 : x = y := by
    first
    | (have i₁ := eq3419994
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3419994
    | exact resolve eq3419994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419994
  have eq3421473 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3421313
       grind)
    | exact superpose eq3421313 eq16
    | exact resolve eq16 eq3421313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421313
  have eq3424353 : False := by grind
  exact eq3424353

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pxx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq48 (τ X0)
       grind)
    | exact superpose eq48 eq18
    | (have j1 := eq48 (τ X0)
       grind)
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq48
  have eq90 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq115 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq289 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 x y
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 x y
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq350 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq36
    | (have j1 := eq90 X0
       grind)
    | exact resolve eq36 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq364 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq350 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350
    | (have j0 := eq350 X0
       grind)
    | exact resolve eq350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq365 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq367 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq365
    | exact resolve eq365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq365 X0
       grind)
    | exact superpose eq365 eq10
    | exact resolve eq10 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq367
    | exact resolve eq367 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq393 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq386 X0
       grind)
    | exact superpose eq386 eq10
    | exact resolve eq10 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq393
    | exact resolve eq393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq441 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0
       have i₂ := eq115 (τ X0) X1
       grind)
    | (have i₁ := eq36 X0
       have i₂ := eq115 (τ X0) (τ X0)
       grind)
    | exact superpose eq115 eq36
    | exact resolve eq36 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq115
  have eq454 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) X1) (τ X0))) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq365 X0
       grind)
    | exact superpose eq365 eq441
    | exact resolve eq441 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq441
  have eq462 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq420 (σ X0)
       grind)
    | exact superpose eq420 eq15
    | exact resolve eq15 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq462 X0
       have i₂ := eq386 X0
       grind)
    | exact superpose eq386 eq462
    | exact resolve eq462 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq494 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq371
    | exact resolve eq371 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq500 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq494 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq494
    | exact resolve eq494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq729 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq289
       have i₂ := eq477 y
       grind)
    | exact superpose eq477 eq289
    | exact resolve eq289 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq730 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq729
       have i₂ := eq477 x
       grind)
    | exact superpose eq477 eq729
    | exact resolve eq729 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq731 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq730
       have i₂ := eq477 y
       grind)
    | exact superpose eq477 eq730
    | exact resolve eq730 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq732 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq731
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq731
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq731 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq733 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq732
  have eq1010 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq454 X0 X1
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq454
    | exact resolve eq454 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq1174 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1010 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1010
    | exact resolve eq1010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1185 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1010 (σ X0) X1
       grind)
    | exact superpose eq1010 eq23
    | exact resolve eq23 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1231 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1185 X0 X1
       have i₂ := eq10 (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq1185
    | exact resolve eq1185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1239 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    grind
  clear eq1174
  have eq1251 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1231 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1231
    | exact resolve eq1231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1255 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1239 X0 X1
       have i₂ := eq477 X0
       grind)
    | exact superpose eq477 eq1239
    | exact resolve eq1239 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1262 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1251 X0 X1
       have i₂ := eq500 X0
       grind)
    | exact superpose eq500 eq1251
    | exact resolve eq1251 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1303 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1262 (σ X0) X1
       grind)
    | exact superpose eq1262 eq23
    | exact resolve eq23 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1262
  have eq1328 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (τ (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1303 X0 X1
       have i₂ := eq500 X0
       grind)
    | exact superpose eq500 eq1303
    | exact resolve eq1303 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq1303
  have eq3832 : ∀ X0 X1 : G, (k (M.op (k X0 X0) (k X0 X0)) (k X0 X0)) = (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1328 (k X0 X0) X1
       have i₂ := eq386 X0
       grind)
    | exact superpose eq386 eq1328
    | exact resolve eq1328 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq3960 : ∀ X0 X1 : G, (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)))) = (M.op (M.op (k X0 X0) (k X0 X0)) (k X0 X0)) := by
    intro X0 X1
    grind
  clear eq3832
  have eq4009 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3960 X0 X1
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq3960
    | exact resolve eq3960 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq3960
  have eq4036 : ∀ X0 X1 : G, (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4009 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq4009
    | exact resolve eq4009 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4009
  have eq10719 : (M.op y y) = (τ (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq733
       grind)
    | exact superpose eq733 eq10
    | exact resolve eq10 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq10782 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10719
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10719
    | exact resolve eq10719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10719
  have eq10783 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq10782
  have eq207762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1255 y y
       have i₂ := eq10783
       grind)
    | exact superpose eq10783 eq1255
    | exact resolve eq1255 eq10783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq10783
  have eq207849 : (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq207762
       have r₂ := eq16
       grind)
    | exact resolve eq207762 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207762
  have eq209559 : ∀ X0 : G, y = (M.op (M.op (M.op x x) X0) (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq9 y x y
       have i₂ := eq207849
       grind)
    | exact superpose eq207849 eq9
    | exact resolve eq9 eq207849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207849
  have eq209660 : x = y ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq209559 x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq209559
    | exact resolve eq209559 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209559
  have eq211136 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq209660
       grind)
    | exact superpose eq209660 eq16
    | exact resolve eq16 eq209660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209660
  have eq211137 : (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq211136
       have r₂ := eq477 x
       grind)
    | exact resolve eq211136 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211136
  have eq211161 : ∀ X0 : G, y = (τ (M.op (M.op (σ (M.op x x)) X0) (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq4036 y x
       have i₂ := eq211137
       grind)
    | exact superpose eq211137 eq4036
    | exact resolve eq4036 eq211137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036 eq211137
  have eq211573 : y = (k (M.op (M.op x x) (M.op x x)) (M.op x x)) := by
    first
    | (have i₁ := eq211161 x
       have i₂ := eq1328 (M.op x x) x
       grind)
    | exact superpose eq1328 eq211161
    | exact resolve eq211161 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq211161
  have eq211595 : y = (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) := by grind
  clear eq211573
  have eq211608 : x = y := by
    first
    | (have i₁ := eq211595
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq211595
    | exact resolve eq211595 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211595
  have eq211618 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211608
       grind)
    | exact superpose eq211608 eq16
    | exact resolve eq16 eq211608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211608
  have eq211619 : False := by grind
  exact eq211619

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_x_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq42 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X2 (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op x X0) X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq48 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (M.op (τ X0) (τ X0)) (τ X0))
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (k X0 (σ (M.op (M.op (τ X0) (τ X0)) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48
    | exact resolve eq48 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq91 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) ≠ X0 ∨ X0 = X1 ∨ (k X1 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq93
    | (have j0 := eq93 (σ X0)
       grind)
    | exact resolve eq93 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (M.op (M.op X0 X0) X1) (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq123 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq123 X1 X1
       grind)
    | exact superpose eq123 eq9
    | exact resolve eq9 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X1 X0 (M.op X0 X1)
       have i₂ := eq123 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq44 X0 X1 (M.op X1 X0)
       have i₂ := eq123 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq123 eq44
    | exact resolve eq44 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op (τ X0) X1) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0
       have i₂ := eq123 (τ X0) X1
       grind)
    | (have i₁ := eq49 X0
       have i₂ := eq123 (τ X0) (τ X0)
       grind)
    | exact superpose eq123 eq49
    | exact resolve eq49 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq293 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op X3 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq42 (M.op (M.op X0 X0) X1) (M.op x X0) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op X3 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq42 (M.op X0 X1) (M.op x (M.op (M.op X0 X0) X0)) X3
       have i₂ := eq42 X0 X1 x
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (M.op (M.op X0 X0) X0) X0 X1
       have i₂ := eq42 X0 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq42 eq44
    | exact resolve eq44 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (M.op (M.op X0 X0) X1)
       have i₂ := eq9 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq91
    | (have j0 := eq91 (M.op (M.op X0 X0) X1) X0
       grind)
    | (have r₁ := eq91 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq9 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq378 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X0)) = X0 ∨ (M.op (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq613 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq218 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq218 X0 X1
       grind)
    | exact superpose eq218 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq218 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq218 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq218 X0 X1
       grind)
    | exact resolve eq13 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq644 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq613 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq645 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq647 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq645
    | (have j0 := eq645 X0 X1
       grind)
    | exact resolve eq645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq958 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq136 (M.op X0 X0) X1 (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq136
    | exact resolve eq136 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1030 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) x
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq43
    | (have j1 := eq94 X0
       grind)
    | exact resolve eq43 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1034 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) X1) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | (have j1 := eq94 X0
       grind)
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq94 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1224 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq958 (M.op X0 X1) (M.op (M.op X0 X0) X0)
       have i₂ := eq42 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq42 eq958
    | exact resolve eq958 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1261 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1224 X0 X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq1224
    | exact resolve eq1224 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1432 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1261 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)
       have i₂ := eq1261 X0 X1
       grind)
    | exact superpose eq1261 eq1261
    | exact resolve eq1261 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1450 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X0 X0) X0) X2
       have i₂ := eq1261 X0 X1
       grind)
    | exact superpose eq1261 eq9
    | exact resolve eq9 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1476 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1432 X0 X1
       have i₂ := eq9 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq1432
    | exact resolve eq1432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1498 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1450 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0) X2
       have i₂ := eq1261 X0 X1
       grind)
    | exact superpose eq1261 eq1450
    | exact resolve eq1450 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261 eq1450
  have eq1706 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X1 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq1476 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq44 X0 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq1476 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq1476 eq44
    | exact resolve eq44 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq2508 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq318 X0 X1
       have i₂ := eq123 X0 X1
       grind)
    | (have i₁ := eq318 X1 X1
       have i₂ := eq123 X1 X1
       grind)
    | exact superpose eq123 eq318
    | exact resolve eq318 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4723 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq647 X0 X1
       have j1 := eq641 X1 X0
       grind)
    | (have r₁ := eq647 X1 X0
       have r₂ := eq641 X0 X1
       grind)
    | (have r₁ := eq647 X1 (k X0 X1)
       have r₂ := eq641 X0 X1
       grind)
    | (have r₁ := eq647 X1 X1
       have r₂ := eq641 X1 X1
       grind)
    | exact resolve eq647 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq647
  have eq4738 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4723 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4723
    | exact resolve eq4723 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4754 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4723 y x
       grind)
    | exact superpose eq4723 eq16
    | (have j1 := eq4723 y x
       grind)
    | exact resolve eq16 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4785 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (M.op (M.op (σ (k X0 X1)) (σ (k X0 X1))) X2) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 (σ X0) (σ X1) X2
       have i₂ := eq4723 X0 X1
       grind)
    | exact superpose eq4723 eq44
    | (have j1 := eq4723 X1 X0
       grind)
    | exact resolve eq44 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq4787 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (σ X0) (σ X1)
       have i₂ := eq4723 X1 X0
       grind)
    | exact superpose eq4723 eq123
    | (have j1 := eq4723 X1 X0
       grind)
    | exact resolve eq123 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4817 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4738 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq4738
    | (have j0 := eq4738 X0 X1
       grind)
    | exact resolve eq4738 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4738
  have eq4821 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4817 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4817
    | exact resolve eq4817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4872 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) ∨ (σ X0) = (M.op (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))) (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq139 (σ X0) X1
       have i₂ := eq4817 (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))) X0
       grind)
    | exact superpose eq4817 eq139
    | (have j1 := eq4817 (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))) X0
       grind)
    | exact resolve eq139 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq4817
  have eq4901 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X1) X0))) ∨ (σ X0) = (M.op (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))) (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4872 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4872
    | (have j0 := eq4872 X0 X1
       grind)
    | exact resolve eq4872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4872
  have eq4915 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X0)) (σ (M.op (M.op X0 X1) X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4901 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4901
    | (have j0 := eq4901 X0 X1
       grind)
    | exact resolve eq4901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4901
  have eq4999 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4821 (τ X0) X1
       grind)
    | exact superpose eq4821 eq18
    | (have j1 := eq4821 (τ X0) X1
       grind)
    | exact resolve eq18 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5158 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4999 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4999
    | exact resolve eq4999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4999
  have eq5216 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5158 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5158
    | (have j0 := eq5158 X0 X1
       grind)
    | exact resolve eq5158 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158
  have eq5308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4754
       have i₂ := eq4821 x y
       grind)
    | exact superpose eq4821 eq4754
    | (have j1 := eq4821 (σ x) (σ y)
       grind)
    | exact resolve eq4754 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4754
  have eq5313 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq5308
  have eq5314 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq5313
       have i₂ := eq4723 y y
       grind)
    | exact superpose eq4723 eq5313
    | (have j1 := eq4723 y y
       grind)
    | exact resolve eq5313 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq5320 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq5313
       grind)
    | exact superpose eq5313 eq36
    | exact resolve eq36 eq5313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5346 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) x (σ y)
       have i₂ := eq5313
       grind)
    | exact superpose eq5313 eq9
    | exact resolve eq9 eq5313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5375 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5320
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5320
    | exact resolve eq5320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320
  have eq5381 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5216 x y
       have i₂ := eq5375
       grind)
    | exact superpose eq5375 eq5216
    | (have j0 := eq5216 x y
       grind)
    | exact resolve eq5216 eq5375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216 eq5375
  have eq5388 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq5381
  have eq5477 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 (M.op x (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)))
       have i₂ := eq295 X0 X1 x
       grind)
    | exact superpose eq295 eq318
    | exact resolve eq318 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq318
  have eq6653 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1706 (σ x) X0 (σ x)
       have i₂ := eq5346 X0
       grind)
    | exact superpose eq5346 eq1706
    | exact resolve eq1706 eq5346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706 eq5346
  have eq24263 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1034 X0 X1
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq1034
    | (have j0 := eq1034 X0 X1
       have j1 := eq93 (σ X0)
       grind)
    | exact resolve eq1034 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq29976 : ∀ X0 X1 : G, (M.op (M.op (σ (τ X0)) (σ (τ X0))) (σ (τ X0))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4787 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq4787
    | (have j0 := eq4787 (τ X0) (τ X1)
       grind)
    | exact resolve eq4787 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq30240 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29976 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29976
    | (have j0 := eq29976 X0 X1
       grind)
    | exact resolve eq29976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29976
  have eq30265 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30240 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq30240
    | (have j0 := eq30240 X0 X1
       grind)
    | exact resolve eq30240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30240
  have eq30278 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op (M.op X0 X0) X0) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30265 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30265
    | (have j0 := eq30265 X0 X1
       grind)
    | exact resolve eq30265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30265
  have eq30285 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30278 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30278
    | (have j0 := eq30278 X0 X1
       grind)
    | exact resolve eq30278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30278
  have eq30590 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X2 (k X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1498 (k X0 X1) X0 X2
       have i₂ := eq30285 X0 X1
       grind)
    | exact superpose eq30285 eq1498
    | (have j1 := eq30285 X0 X1
       grind)
    | exact resolve eq1498 eq30285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30285
  have eq30653 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30590 X0 X1 X2
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq30590
    | (have j0 := eq30590 X0 X1 X2
       grind)
    | exact resolve eq30590 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30590
  have eq34717 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1))) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1))) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5477 X0 (M.op x (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)))
       have i₂ := eq293 X0 X1 x
       grind)
    | exact superpose eq293 eq5477
    | exact resolve eq5477 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq5477
  have eq35075 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1))) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34717 X0 X1
       have i₂ := eq2508 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq2508 eq34717
    | exact resolve eq34717 eq2508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508 eq34717
  have eq35137 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 (M.op (M.op X0 X0) X1))) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35075 X0 X1
       have i₂ := eq132 X0 X1
       grind)
    | exact superpose eq132 eq35075
    | exact resolve eq35075 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq35075
  have eq41540 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (M.op (M.op (σ (τ (k X0 X1))) (σ (τ (k X0 X1)))) X2) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4785 (τ X1) (τ X0) X2
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq4785
    | (have j0 := eq4785 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq4785 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq4785
  have eq41770 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (M.op (M.op (σ (τ (k X0 X1))) (σ (τ (k X0 X1)))) X2) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41540 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq41540
    | (have j0 := eq41540 X0 X1 X2
       grind)
    | exact resolve eq41540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41540
  have eq41796 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (M.op (M.op (k X0 X1) (k X0 X1)) X2) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41770 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq41770
    | (have j0 := eq41770 X0 X1 X2
       grind)
    | exact resolve eq41770 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41770
  have eq41812 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op (M.op (M.op (k X0 X1) (k X0 X1)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41796 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41796
    | (have j0 := eq41796 X0 X1 X2
       grind)
    | exact resolve eq41796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41796
  have eq41818 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (M.op (M.op (k X0 X1) (k X0 X1)) X2) X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41812 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41812
    | (have j0 := eq41812 X0 X1 X2
       grind)
    | exact resolve eq41812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41812
  have eq227823 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op y y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq5314
       grind)
    | exact superpose eq5314 eq36
    | exact resolve eq36 eq5314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5314
  have eq228002 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq227823
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq227823
    | exact resolve eq227823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227823
  have eq228056 : (k y y) = (τ (σ x)) ∨ x = (M.op y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq228002
       grind)
    | exact superpose eq228002 eq10
    | exact resolve eq10 eq228002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228002
  have eq228224 : y = (k y y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq228056
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq228056
    | exact resolve eq228056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228056
  have eq228242 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq228224
       have i₂ := eq4821 y y
       grind)
    | exact superpose eq4821 eq228224
    | (have j1 := eq4821 y y
       grind)
    | exact resolve eq228224 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821 eq228224
  have eq228458 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq228242
  have eq228577 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq228458
  have eq228820 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1045 y
       have i₂ := eq228577
       grind)
    | exact superpose eq228577 eq1045
    | (have j0 := eq1045 y
       grind)
    | exact resolve eq1045 eq228577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq228577
  have eq228946 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq228820
  have eq231844 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq6653 X0
       have i₂ := eq228946
       grind)
    | exact superpose eq228946 eq6653
    | exact resolve eq6653 eq228946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6653 eq228946
  have eq232006 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq231844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231844
  have eq237414 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5313
       have i₂ := eq232006 (σ y)
       grind)
    | exact superpose eq232006 eq5313
    | exact resolve eq5313 eq232006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5313 eq232006
  have eq237752 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq237414
  have eq237803 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq237752
       grind)
    | exact superpose eq237752 eq16
    | exact resolve eq16 eq237752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237752
  have eq237914 : x = (M.op y y) := by
    first
    | (have r₁ := eq237803
       have r₂ := eq5388
       grind)
    | exact resolve eq237803 eq5388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5388 eq237803
  have eq237981 : ∀ X0 X1 : G, y = (M.op (M.op x X0) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 X1
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq9
    | exact resolve eq9 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237986 : y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq45
    | exact resolve eq45 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq238005 : ∀ X0 : G, y = (k (M.op x X0) (M.op x y)) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq378 y x
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq378
    | exact resolve eq378 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq238008 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq958 y x
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq958
    | exact resolve eq958 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq238057 : ∀ X0 : G, y = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq9 y x y
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq9
    | exact resolve eq9 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238058 : x ≠ x ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq13
    | exact resolve eq13 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238086 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq1498 y X0 y
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq1498
    | exact resolve eq1498 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq238133 : x = (k y y) ∨ x = y := by grind
  clear eq238058
  have eq242655 : ∀ X0 : G, (M.op x (k y X0)) = (M.op (k y X0) (k y X0)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq238008 (k y X0)
       have i₂ := eq30653 y X0 x
       grind)
    | exact superpose eq30653 eq238008
    | (have j1 := eq30653 (M.op x (k y X0)) (k y X0) x
       grind)
    | exact resolve eq238008 eq30653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30653 eq238008
  have eq311199 : ∀ X0 X1 : G, (k y X0) = (M.op (M.op (M.op x (k y X0)) X1) X0) ∨ (M.op X0 X0) = y ∨ (M.op X0 X0) = y := by
    intro X0 X1
    first
    | (have i₁ := eq41818 y X0 X1
       have i₂ := eq242655 X0
       grind)
    | exact superpose eq242655 eq41818
    | (have j0 := eq41818 y X0 x
       have j1 := eq242655 X0
       grind)
    | exact resolve eq41818 eq242655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41818 eq242655
  have eq311395 : ∀ X0 X1 : G, (k y X0) = (M.op (M.op (M.op x (k y X0)) X1) X0) ∨ (M.op X0 X0) = y := by
    intro X0 X1
    first
    | (have j0 := eq311199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311199
  have eq329939 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq311395 (M.op X0 x) x
       have i₂ := eq135 x (k y (M.op X0 x)) X0
       grind)
    | exact superpose eq135 eq311395
    | (have j0 := eq311395 (M.op X0 x) x
       grind)
    | exact resolve eq311395 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq311395
  have eq330848 : ∀ X0 : G, y = (k y (M.op X0 x)) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    grind
  clear eq329939
  have eq335858 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq330848 (M.op (M.op y x) (M.op y x))
       have i₂ := eq238086 x
       grind)
    | exact superpose eq238086 eq330848
    | exact resolve eq330848 eq238086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238086 eq330848
  have eq336417 : x ≠ y ∨ x = (k y y) := by grind
  clear eq335858
  have eq336433 : x = (k y y) := by
    first
    | (have r₁ := eq336417
       have r₂ := eq238133
       grind)
    | exact resolve eq336417 eq238133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238133 eq336417
  have eq336738 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1030 y x
       have i₂ := eq336433
       grind)
    | exact superpose eq336433 eq1030
    | (have j0 := eq1030 y x
       grind)
    | exact resolve eq1030 eq336433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq336742 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1034 y x
       have i₂ := eq336433
       grind)
    | exact superpose eq336433 eq1034
    | (have j0 := eq1034 y x
       grind)
    | exact resolve eq1034 eq336433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq531677 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq336738 (M.op (σ x) x)
       have i₂ := eq336742 x
       grind)
    | exact superpose eq336742 eq336738
    | exact resolve eq336738 eq336742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336738 eq336742
  have eq531786 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq531677
  have eq531871 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq532088 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq531786
  have eq532113 : (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq531871
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq531871
    | exact resolve eq531871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531871
  have eq532121 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq532113
       have i₂ := eq336433
       grind)
    | exact superpose eq336433 eq532113
    | exact resolve eq532113 eq336433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532113
  have eq532514 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq532121
       have r₂ := eq532088
       grind)
    | exact resolve eq532121 eq532088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532088 eq532121
  have eq532578 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq123 (σ y) X0
       have i₂ := eq532514
       grind)
    | exact superpose eq532514 eq123
    | exact resolve eq123 eq532514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq532514
  have eq596185 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24263 (M.op x y) x
       have i₂ := eq237981 y x
       grind)
    | exact superpose eq237981 eq24263
    | (have j0 := eq24263 (M.op x y) x
       grind)
    | exact resolve eq24263 eq237981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24263 eq237981
  have eq596662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq596185 x
       have i₂ := eq532578 x
       grind)
    | exact superpose eq532578 eq596185
    | exact resolve eq596185 eq532578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532578 eq596185
  have eq596730 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq596662
       have r₂ := eq16
       grind)
    | exact resolve eq596662 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596662
  have eq615571 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op x X0) (M.op y (M.op x X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq35137 y x
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq35137
    | exact resolve eq35137 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35137
  have eq674515 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36 (M.op x y)
       have i₂ := eq596730
       grind)
    | exact superpose eq596730 eq36
    | exact resolve eq36 eq596730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq596730
  have eq674813 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq674515
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq674515
    | exact resolve eq674515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674515
  have eq674904 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq238005 y
       have i₂ := eq674813
       grind)
    | exact superpose eq674813 eq238005
    | (have j0 := eq238005 y
       grind)
    | exact resolve eq238005 eq674813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238005 eq674813
  have eq675110 : y = (M.op x y) := by grind
  clear eq674904
  have eq676502 : y = (k y y) := by
    first
    | (have i₁ := eq237986
       have i₂ := eq675110
       grind)
    | exact superpose eq675110 eq237986
    | exact resolve eq237986 eq675110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237986
  have eq676635 : y = (M.op y x) := by
    first
    | (have i₁ := eq238057 y
       have i₂ := eq675110
       grind)
    | exact superpose eq675110 eq238057
    | exact resolve eq238057 eq675110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238057
  have eq676965 : x = y := by
    first
    | (have i₁ := eq676502
       have i₂ := eq336433
       grind)
    | exact superpose eq336433 eq676502
    | exact resolve eq676502 eq336433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336433 eq676502
  have eq677126 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq676965
       grind)
    | exact superpose eq676965 eq16
    | exact resolve eq16 eq676965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680269 : x = (M.op x x) := by
    first
    | (have i₁ := eq676635
       have i₂ := eq676965
       grind)
    | exact superpose eq676965 eq676635
    | exact resolve eq676635 eq676965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676635
  have eq681113 : (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq4915 (M.op x y) (M.op y (M.op x y))
       have i₂ := eq615571 y
       grind)
    | exact superpose eq615571 eq4915
    | exact resolve eq4915 eq615571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915 eq615571
  have eq681642 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq681113
       have i₂ := eq675110
       grind)
    | exact superpose eq675110 eq681113
    | exact resolve eq681113 eq675110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681113
  have eq682146 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq681642
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq681642
    | exact resolve eq681642 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681642
  have eq682538 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq682146
       have i₂ := eq676965
       grind)
    | exact superpose eq676965 eq682146
    | exact resolve eq682146 eq676965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682146
  have eq682773 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq682538
       have i₂ := eq675110
       grind)
    | exact superpose eq675110 eq682538
    | exact resolve eq682538 eq675110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675110 eq682538
  have eq682899 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq682773
       have i₂ := eq237914
       grind)
    | exact superpose eq237914 eq682773
    | exact resolve eq682773 eq237914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237914 eq682773
  have eq682985 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq682899
       have i₂ := eq676965
       grind)
    | exact superpose eq676965 eq682899
    | exact resolve eq682899 eq676965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676965 eq682899
  have eq682986 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq682985
  have eq734745 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq677126
       have i₂ := eq680269
       grind)
    | exact superpose eq680269 eq677126
    | exact resolve eq677126 eq680269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677126 eq680269
  have eq734746 : False := by grind
  exact eq734746
