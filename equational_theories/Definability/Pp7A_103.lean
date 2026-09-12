import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_pxy_pxx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq85 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq198 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq434 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq466 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq434
    | (have j0 := eq434 X0 X1
       grind)
    | exact resolve eq434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq890 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq75
  have eq897 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq890 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq890
    | (have j0 := eq890 X0
       grind)
    | exact resolve eq890 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq890
  have eq898 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq909 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq198
       have i₂ := eq466 y x
       grind)
    | exact superpose eq466 eq198
    | (have j1 := eq466 (σ x) (σ y)
       grind)
    | (have r₁ := eq198
       have r₂ := eq466 y x
       grind)
    | (have r₁ := eq198
       have r₂ := eq466 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq198
       have r₂ := eq466 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq198 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq466
  have eq910 : x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq909
  have eq912 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq898 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq898
    | exact resolve eq898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq940 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq912 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq912
    | exact resolve eq912 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq912
  have eq945 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq940 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq940
    | exact resolve eq940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq965 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq945 (σ X0)
       grind)
    | exact superpose eq945 eq15
    | exact resolve eq15 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq965 X0
       have i₂ := eq945 X0
       grind)
    | exact superpose eq945 eq965
    | exact resolve eq965 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq965
  have eq1076 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq1087 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1076 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1076
    | exact resolve eq1076 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1099 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq1087
  have eq44142 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq16
    | exact resolve eq16 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq44143 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq44142
       have r₂ := eq983 x
       grind)
    | exact resolve eq44142 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44142
  have eq44144 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq44143
       have i₂ := eq983 x
       grind)
    | exact superpose eq983 eq44143
    | exact resolve eq44143 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44143
  have eq44685 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq44144
       grind)
    | exact superpose eq44144 eq10
    | exact resolve eq10 eq44144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44144
  have eq44810 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq44685
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq44685
    | exact resolve eq44685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44685
  have eq44837 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44810
       grind)
    | exact superpose eq44810 eq16
    | exact resolve eq16 eq44810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44810
  have eq44838 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq44837
       have r₂ := eq983 x
       grind)
    | exact resolve eq44837 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq44837
  have eq45275 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq44838
       grind)
    | exact superpose eq44838 eq10
    | exact resolve eq10 eq44838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44838
  have eq45400 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45275
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq45275
    | exact resolve eq45275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45275
  have eq45401 : y = (M.op x x) := by grind
  clear eq45400
  have eq45445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1099 x
       have i₂ := eq45401
       grind)
    | exact superpose eq45401 eq1099
    | exact resolve eq1099 eq45401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq45401
  have eq45578 : False := by grind
  exact eq45578

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_x_pxy_x_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq24 eq35
  have eq71 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
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
  have eq72 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq44
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123 eq80
    | (have j0 := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq190
    | exact resolve eq190 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq194 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq191
       have r₂ := eq27
       grind)
    | exact resolve eq191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq196 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq194
    | exact resolve eq194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq198 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq27
    | exact resolve eq27 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq72
    | (have r₁ := eq72
       have r₂ := eq196
       grind)
    | exact resolve eq72 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq196
  have eq473 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq472
  have eq476 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq473 eq123
    | exact resolve eq123 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq480 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq476
  have eq485 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq480
       have r₂ := eq198
       grind)
    | exact resolve eq480 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq480
  have eq489 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq485 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq492 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq80 (σ x) (σ y)
       grind)
    | (have r₁ := eq489
       have r₂ := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq489 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq495 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq492
    | exact resolve eq492 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq495 eq123
    | exact resolve eq123 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq495
  have eq575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq572
  have eq579 : x = (M.op x y) := by
    first
    | (have r₁ := eq575
       have r₂ := eq27
       grind)
    | exact resolve eq575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq581 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq579 eq20
    | exact resolve eq20 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq583 : x ≠ x ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq579 eq71
    | (have r₁ := eq71
       have r₂ := eq579
       grind)
    | exact resolve eq71 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq590 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq583
  have eq598 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq581
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq581
    | exact resolve eq581 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq601 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq598 eq26
    | exact resolve eq26 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq715 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq590
       grind)
    | exact superpose eq590 eq44
    | exact resolve eq44 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq722 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq598 eq715
    | exact resolve eq715 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq724 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq722
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq722
    | exact resolve eq722 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq725 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq598 eq724
    | exact resolve eq724 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq728 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq725 eq80
    | (have j0 := eq80 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq80 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq729 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq728
  have eq731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq601 eq729
    | exact resolve eq729 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq734 : x = (M.op y x) := by
    first
    | (have r₁ := eq731
       have r₂ := eq27
       grind)
    | exact resolve eq731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq739 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq734
       grind)
    | exact superpose eq734 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq742 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq80 x y
       grind)
    | (have r₁ := eq739
       have r₂ := eq80 x y
       grind)
    | exact resolve eq739 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq745 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq742
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq742
    | exact resolve eq742 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq742
  have eq746 : x = (k x y) := by
    first
    | exact superpose eq579 eq745
    | exact resolve eq745 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq745
  have eq825 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq746
       grind)
    | exact superpose eq746 eq44
    | exact resolve eq44 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq746
  have eq832 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq598 eq825
    | exact resolve eq825 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq834 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq832
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq832
    | exact resolve eq832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq832
  have eq835 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq598 eq834
    | exact resolve eq834 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq834
  have eq905 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq835 eq80
    | (have j0 := eq80 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq80 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq835
  have eq906 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq905
  have eq908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq601 eq906
    | exact resolve eq906 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq906
  have eq911 : False := by grind
  exact eq911

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxy_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq515 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq518 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq1103 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq518 x y
       grind)
    | exact superpose eq518 eq16
    | (have j1 := eq518 x y
       grind)
    | exact resolve eq16 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq518 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3990 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq515 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq515
    | exact resolve eq515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq4115 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3990 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3990
    | (have j0 := eq3990 X0 X1
       grind)
    | exact resolve eq3990 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990
  have eq9142 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1103
       have i₂ := eq4115 x y
       grind)
    | exact superpose eq4115 eq1103
    | (have j1 := eq4115 (σ x) (σ y)
       grind)
    | (have r₁ := eq1103
       have r₂ := eq4115 x y
       grind)
    | (have r₁ := eq1103
       have r₂ := eq4115 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1103
       have r₂ := eq4115 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1103 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq9143 : x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq9142
  have eq10827 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1106 X1 X0
       have i₂ := eq518 X0 X1
       grind)
    | exact superpose eq518 eq1106
    | (have j0 := eq1106 X0 X1
       have j1 := eq518 X0 X1
       grind)
    | (have r₁ := eq1106 X0 X0
       have r₂ := eq518 X0 X0
       grind)
    | exact resolve eq1106 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq10832 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10827 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10827
  have eq10836 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10832 X0 X1
       have j1 := eq1106 X0 X1
       grind)
    | (have r₁ := eq10832 X0 X1
       have r₂ := eq1106 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq10832 X0 X1
       have r₂ := eq1106 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq10832 X1 X0
       have r₂ := eq1106 X0 X1
       grind)
    | exact resolve eq10832 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq10832
  have eq26340 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9143
       grind)
    | exact superpose eq9143 eq16
    | exact resolve eq16 eq9143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9143
  have eq26341 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq26340
       have r₂ := eq77 x
       grind)
    | exact resolve eq26340 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26340
  have eq26343 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq26341
       grind)
    | exact superpose eq26341 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq26341
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26341
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26341
       grind)
    | exact resolve eq12 eq26341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26341
  have eq26344 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by grind
  clear eq26343
  have eq26347 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq26344
       grind)
    | exact superpose eq26344 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26344
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26344
       grind)
    | exact resolve eq12 eq26344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26348 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq26344
       grind)
    | exact superpose eq26344 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26344
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26344
       grind)
    | exact resolve eq12 eq26344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26344
  have eq26349 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by grind
  clear eq26348
  have eq26350 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by grind
  clear eq26347
  have eq26352 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq26349
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq26349
    | exact resolve eq26349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26349
  have eq26353 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq26350
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq26350
    | exact resolve eq26350 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26350
  have eq26380 : (σ (k y x)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq26352
       have i₂ := eq26353
       grind)
    | exact superpose eq26353 eq26352
    | exact resolve eq26352 eq26353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26352 eq26353
  have eq26395 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq26380
  have eq26404 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1103
       have i₂ := eq26395
       grind)
    | exact superpose eq26395 eq1103
    | exact resolve eq1103 eq26395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq26416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq26404
  have eq26417 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq26416
  have eq26420 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq10836 x y
       grind)
    | (have r₁ := eq26417
       have r₂ := eq10836 y x
       grind)
    | (have r₁ := eq26417
       have r₂ := eq10836 x y
       grind)
    | exact resolve eq26417 eq10836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10836 eq26417
  have eq26423 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq26420
       grind)
    | exact superpose eq26420 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26420
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26420
       grind)
    | exact resolve eq12 eq26420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26420
  have eq26424 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq26423
  have eq26427 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26424
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq26424
    | exact resolve eq26424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26424
  have eq26432 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26427
       grind)
    | exact superpose eq26427 eq16
    | exact resolve eq16 eq26427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26427
  have eq26455 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq26432
       have i₂ := eq26395
       grind)
    | exact superpose eq26395 eq26432
    | exact resolve eq26432 eq26395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26395
  have eq26460 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq26455
  have eq26461 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq26460
  have eq26463 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26461
       grind)
    | exact superpose eq26461 eq10
    | exact resolve eq10 eq26461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26461
  have eq26677 : x = y ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq26463
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26463
    | exact resolve eq26463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26463
  have eq26679 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26677
       grind)
    | exact superpose eq26677 eq16
    | exact resolve eq16 eq26677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26677
  have eq26680 : (σ (k y x)) = (σ (k x y)) := by
    first
    | (have r₁ := eq26679
       have r₂ := eq77 x
       grind)
    | exact resolve eq26679 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26679
  have eq26684 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26432
       have i₂ := eq26680
       grind)
    | exact superpose eq26680 eq26432
    | exact resolve eq26432 eq26680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26432
  have eq26696 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq26680
       grind)
    | exact superpose eq26680 eq10
    | exact resolve eq10 eq26680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26680
  have eq26912 : (k y x) = (k x y) := by
    first
    | (have i₁ := eq26696
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq26696
    | exact resolve eq26696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26696
  have eq26918 : (M.op x y) = (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq26912
       grind)
    | exact superpose eq26912 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq26912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26912
  have eq26964 : x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq26918
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq26918
       have r₂ := eq12 y x
       grind)
    | exact resolve eq26918 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26918
  have eq26971 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26964
       grind)
    | exact superpose eq26964 eq16
    | exact resolve eq16 eq26964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26964
  have eq26972 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq26971
       have r₂ := eq77 x
       grind)
    | exact resolve eq26971 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26971
  have eq29204 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26684
       have i₂ := eq26972
       grind)
    | exact superpose eq26972 eq26684
    | exact resolve eq26684 eq26972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26684 eq26972
  have eq29207 : (σ x) = (σ y) := by grind
  clear eq29204
  have eq29208 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29207
       grind)
    | exact superpose eq29207 eq16
    | exact resolve eq16 eq29207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29209 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29207
       grind)
    | exact superpose eq29207 eq10
    | exact resolve eq10 eq29207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29207
  have eq29423 : x = y := by
    first
    | (have i₁ := eq29209
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29209
    | exact resolve eq29209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29209
  have eq29424 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29208
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq29208
    | exact resolve eq29208 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq29208
  have eq29425 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29424
       have i₂ := eq29423
       grind)
    | exact superpose eq29423 eq29424
    | exact resolve eq29424 eq29423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29423 eq29424
  have eq29426 : False := by grind
  exact eq29426

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pxy_pyx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq22
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq110 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq65
    | exact resolve eq65 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq65
  have eq538 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (M.op (σ X0) (k X1 (σ X2))) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq110 X0 X1 X2
       grind)
    | exact superpose eq110 eq13
    | (have j0 := eq13 (σ X0) (k X1 (σ X2))
       have j1 := eq110 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq110 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq110 X0 X1 X2
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq547 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq538 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq553 : ∀ X0 X1 X2 : G, (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq547 X0 X1 X2
       have j1 := eq12 (σ X0) (k X1 (σ X2))
       grind)
    | (have r₁ := eq547 X0 X1 X2
       have r₂ := eq12 (σ X0) (k X1 (σ X2))
       grind)
    | exact resolve eq547 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq565 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq553 X0 X1 X2
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq553
    | (have j0 := eq553 X0 X1 X2
       grind)
    | exact resolve eq553 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq553
  have eq566 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq565 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq1008 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq566 (τ X0) X1 (τ X2)
       have i₂ := eq35 (τ X1) X2 X0
       grind)
    | exact superpose eq35 eq566
    | exact resolve eq566 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq566
  have eq1066 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1008 X0 X1 X2
       have i₂ := eq11 (k X0 (k (σ (τ X1)) X2))
       grind)
    | exact superpose eq11 eq1008
    | exact resolve eq1008 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1087 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op (σ (τ X0)) (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1066 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq1066
    | exact resolve eq1066 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1097 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1087 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1087
    | exact resolve eq1087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1101 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1097 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1097
    | exact resolve eq1097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1104 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1101 X0 X0 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq1101
    | exact resolve eq1101 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1164 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X1))) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1101 X0 X1 (M.op X0 X0)
       have i₂ := eq1104 X0 X1
       grind)
    | exact superpose eq1104 eq1101
    | exact resolve eq1101 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101 eq1104
  have eq15842 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1164 X0 (M.op X0 X0) x
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq1164
    | exact resolve eq1164 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq16028 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq15842 (σ X1) (σ X0)
       grind)
    | exact superpose eq15842 eq15
    | exact resolve eq15 eq15842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16076 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16028 X0 X1
       have i₂ := eq15842 X1 X0
       grind)
    | exact superpose eq15842 eq16028
    | exact resolve eq16028 eq15842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15842 eq16028
  have eq16991 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16076 x y
       grind)
    | exact superpose eq16076 eq16
    | (have r₁ := eq16
       have r₂ := eq16076 x y
       grind)
    | exact resolve eq16 eq16076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16076
  have eq17059 : False := by grind
  exact eq17059

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq73 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq74 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq91 y x
       grind)
    | exact superpose eq91 eq70
    | (have j1 := eq91 y x
       grind)
    | exact resolve eq70 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq91 sF3 sF2
       grind)
    | exact superpose eq91 eq80
    | (have j1 := eq91 (σ y) (σ x)
       grind)
    | exact resolve eq80 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq113 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq110
    | exact resolve eq110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq115 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq113
    | exact resolve eq113 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq91
    | (have j0 := eq91 (σ y) (σ x)
       grind)
    | exact resolve eq91 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq27
    | exact resolve eq27 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq147 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq406 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq70
    | exact resolve eq70 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq115
  have eq409 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq406
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq406
    | exact resolve eq406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq495 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq74
    | (have r₁ := eq74
       have r₂ := eq126
       grind)
    | exact resolve eq74 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq126
  have eq496 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq495
  have eq501 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq496 eq117
    | exact resolve eq117 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq505 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq501
  have eq512 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq505
       have r₂ := eq128
       grind)
    | exact resolve eq505 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq505
  have eq516 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq512 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq512
       grind)
    | exact resolve eq13 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq517 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq516
  have eq518 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq517
    | exact resolve eq517 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq517
  have eq582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq518 eq117
    | exact resolve eq117 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq518
  have eq585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq582
  have eq589 : y = (M.op x y) := by
    first
    | (have r₁ := eq585
       have r₂ := eq27
       grind)
    | exact resolve eq585 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq591 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq589 eq20
    | exact resolve eq20 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq595 : y ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq589 eq73
    | (have r₁ := eq73
       have r₂ := eq589
       grind)
    | exact resolve eq73 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq601 : y = (M.op y x) ∨ y = (k y x) := by grind
  clear eq595
  have eq609 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq591
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq591
    | exact resolve eq591 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq622 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq609 eq409
    | exact resolve eq409 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq627 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq622
       have r₂ := eq27
       grind)
    | exact resolve eq622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq639 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq627 eq147
    | exact resolve eq147 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq627
  have eq641 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq589 eq639
    | exact resolve eq639 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq839 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq601
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq601
    | exact resolve eq601 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq841 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq839
       grind)
    | exact superpose eq839 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq839
       grind)
    | exact resolve eq13 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq842 : (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq841
  have eq843 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq842
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq842
    | exact resolve eq842 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq842
  have eq845 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq843
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq843
    | exact resolve eq843 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq843
  have eq847 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq589 eq845
    | exact resolve eq845 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq845
  have eq848 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq847
  have eq851 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq848 eq15
    | exact resolve eq15 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq871 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq851
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq851
    | exact resolve eq851 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq851
  have eq877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq609 eq871
    | exact resolve eq871 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq871
  have eq880 : False := by grind
  exact eq880

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq30 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq42
  have eq50 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq48
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq97 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       have j1 := eq50 X1 X0
       grind)
    | (have r₁ := eq93 X1 X0
       have r₂ := eq50 X0 X1
       grind)
    | (have r₁ := eq93 X1 X1
       have r₂ := eq50 X1 X1
       grind)
    | exact resolve eq93 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq93
  have eq203 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq97 (σ X1) (σ X0)
       grind)
    | exact superpose eq97 eq15
    | exact resolve eq15 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq203
    | exact resolve eq203 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq203
  have eq212 : False := by grind
  exact eq212

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq73 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq123 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (k X0 (σ X1)) (σ X2)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq14
    | (have j0 := eq14 (k X0 (σ X1)) (σ X2)
       grind)
    | exact resolve eq14 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq12
    | (have j1 := eq73 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq73 X0
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq742 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq743 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq742 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq742
    | (have j0 := eq742 X0
       grind)
    | exact resolve eq742 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq742
  have eq747 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq743 X0
       have j1 := eq741 X0
       grind)
    | (have r₁ := eq743 X0
       have r₂ := eq741 X0
       grind)
    | exact resolve eq743 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq743
  have eq757 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq747 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq747
    | exact resolve eq747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (k X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq747 X0
       grind)
    | exact superpose eq747 eq9
    | exact resolve eq9 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq757 X0
       have i₂ := eq24 (σ X0) X0
       grind)
    | exact superpose eq24 eq757
    | exact resolve eq757 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq785 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq782 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq782
    | exact resolve eq782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq803 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq785 (σ X0)
       grind)
    | exact superpose eq785 eq15
    | exact resolve eq15 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq803 X0
       have i₂ := eq785 X0
       grind)
    | exact superpose eq785 eq803
    | exact resolve eq803 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq943 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ (k X1 X1)) (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq768 X1 (τ X0)
       have i₂ := eq747 X0
       grind)
    | exact superpose eq747 eq768
    | exact resolve eq768 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq950 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ (k X1 X1)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq943 X0 X1
       have i₂ := eq785 X0
       grind)
    | exact superpose eq785 eq943
    | exact resolve eq943 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq962 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X1 X1)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 X1
       have i₂ := eq785 X1
       grind)
    | exact superpose eq785 eq950
    | exact resolve eq950 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq39977 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (k X1 (σ X2))) = (k (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (k X1 (σ X2)) ∨ (M.op (σ X0) (k X1 (σ X2))) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (k X1 (σ X2)) (σ X0)
       have i₂ := eq123 X1 X2 X0
       grind)
    | exact superpose eq123 eq12
    | (have j0 := eq12 (k X1 (σ X2)) (σ X0)
       have j1 := eq123 X1 X2 X0
       grind)
    | (have r₁ := eq12 (k X0 (σ X1)) (σ X2)
       have r₂ := eq123 X0 X1 X2
       grind)
    | exact resolve eq12 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq39978 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) = (k (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (k X1 (σ X2)) ∨ (M.op (σ X0) (k X1 (σ X2))) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39977 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39977
  have eq39982 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (k X1 (σ X2)) ∨ (M.op (σ X0) (k X1 (σ X2))) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39978 X0 X1 X2
       have i₂ := eq23 X1 X2 X0
       grind)
    | exact superpose eq23 eq39978
    | (have j0 := eq39978 X0 X1 X2
       grind)
    | exact resolve eq39978 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq39978
  have eq39983 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39982 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39982
  have eq40332 : ∀ X0 X1 X2 : G, (k (σ (k (τ X1) X2)) X0) = (M.op (σ (τ X0)) (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k (τ X1) X2)
       have i₂ := eq39983 (τ X0) X1 X2
       grind)
    | exact superpose eq39983 eq19
    | (have j1 := eq39983 (τ X0) X1 X2
       grind)
    | exact resolve eq19 eq39983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39983
  have eq40450 : ∀ X0 X1 X2 : G, (k (σ (k (τ X1) X2)) X0) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40332 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40332
    | (have j0 := eq40332 X0 X1 X2
       grind)
    | exact resolve eq40332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40332
  have eq40528 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40450 X0 X1 X2
       have i₂ := eq18 X1 X2
       grind)
    | exact superpose eq18 eq40450
    | (have j0 := eq40450 X0 X1 X2
       grind)
    | exact resolve eq40450 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq40450
  have eq40600 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op X0 (k X1 (σ X2))) ∨ (k X1 (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40528 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40528
    | (have j0 := eq40528 X0 X1 X2
       grind)
    | exact resolve eq40528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40528
  have eq40796 : ∀ X0 X1 X2 : G, (k (k X1 X0) X2) = (M.op X2 (k X1 X0)) ∨ (k X1 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40600 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40600
    | exact resolve eq40600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40600
  have eq41444 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40796 X0 X0 x
       have i₂ := eq785 X0
       grind)
    | exact superpose eq785 eq40796
    | (have j0 := eq40796 X1 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       grind)
    | exact resolve eq40796 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41721 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = (σ (M.op (τ X0) (M.op X1 X1))) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (M.op X1 X1)
       have i₂ := eq41444 X1 (τ X0)
       grind)
    | exact superpose eq41444 eq19
    | (have j1 := eq41444 X1 (τ X0)
       grind)
    | exact resolve eq19 eq41444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49191 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) X0) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq41721 X0 (τ (M.op X0 X0))
       have i₂ := eq962 X0 X0
       grind)
    | exact superpose eq962 eq41721
    | (have j0 := eq41721 X0 (τ (M.op X0 X0))
       grind)
    | exact resolve eq41721 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962 eq41721
  have eq49311 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ (k (M.op X0 X0) (M.op X0 X0)))) X0) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49191 X0
       have i₂ := eq747 (M.op X0 X0)
       grind)
    | exact superpose eq747 eq49191
    | (have j0 := eq49191 X0
       grind)
    | exact resolve eq49191 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49191
  have eq49334 : ∀ X0 : G, (σ (τ X0)) = (k (k (M.op X0 X0) (M.op X0 X0)) X0) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49311 X0
       have i₂ := eq11 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq49311
    | (have j0 := eq49311 X0
       grind)
    | exact resolve eq49311 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49311
  have eq49342 : ∀ X0 : G, (σ (τ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49334 X0
       have i₂ := eq785 (M.op X0 X0)
       grind)
    | exact superpose eq785 eq49334
    | (have j0 := eq49334 X0
       grind)
    | exact resolve eq49334 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49334
  have eq49348 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49342 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49342
    | (have j0 := eq49342 X0
       grind)
    | exact resolve eq49342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49342
  have eq49353 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49348 X0
       have i₂ := eq747 (M.op X0 X0)
       grind)
    | exact superpose eq747 eq49348
    | (have j0 := eq49348 X0
       grind)
    | exact resolve eq49348 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq49348
  have eq49357 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49353 X0
       have i₂ := eq785 (M.op X0 X0)
       grind)
    | exact superpose eq785 eq49353
    | (have j0 := eq49353 X0
       grind)
    | exact resolve eq49353 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq49353
  have eq120132 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) X0) ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) X0
       have i₂ := eq49357 (σ X0)
       grind)
    | exact superpose eq49357 eq24
    | (have j1 := eq49357 (σ X0)
       grind)
    | exact resolve eq24 eq49357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq49357
  have eq120301 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) X0) ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120132 X0
       have i₂ := eq821 X0
       grind)
    | exact superpose eq821 eq120132
    | (have j0 := eq120132 X0
       grind)
    | exact resolve eq120132 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120132
  have eq120382 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) X0) ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120301 X0
       have i₂ := eq821 (M.op X0 X0)
       grind)
    | exact superpose eq821 eq120301
    | (have j0 := eq120301 X0
       grind)
    | exact resolve eq120301 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120301
  have eq120450 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120382 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq120382
    | (have j0 := eq120382 X0
       grind)
    | exact resolve eq120382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120382
  have eq120517 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120450 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120450
    | (have j0 := eq120450 X0
       grind)
    | exact resolve eq120450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120450
  have eq120574 : ∀ X0 : G, (τ (σ X0)) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120517 X0
       have i₂ := eq821 X0
       grind)
    | exact superpose eq821 eq120517
    | (have j0 := eq120517 X0
       grind)
    | exact resolve eq120517 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120517
  have eq120630 : ∀ X0 : G, (τ (σ X0)) = (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120574 X0
       have i₂ := eq821 (M.op X0 X0)
       grind)
    | exact superpose eq821 eq120574
    | (have j0 := eq120574 X0
       grind)
    | exact resolve eq120574 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120574
  have eq120684 : ∀ X0 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120630 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq120630
    | (have j0 := eq120630 X0
       grind)
    | exact resolve eq120630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120630
  have eq120731 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq120684 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120684
    | (have j0 := eq120684 X0
       grind)
    | exact resolve eq120684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120684
  have eq121045 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40796 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       have i₂ := eq120731 X0
       grind)
    | exact superpose eq120731 eq40796
    | (have j0 := eq40796 X1 X0 (M.op X1 X0)
       have j1 := eq120731 X0
       grind)
    | exact resolve eq40796 eq120731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40796 eq120731
  have eq122082 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41444 (M.op X0 X0) X1
       have i₂ := eq121045 X0 X1
       grind)
    | exact superpose eq121045 eq41444
    | (have j1 := eq121045 X0 X1
       grind)
    | exact resolve eq41444 eq121045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41444 eq121045
  have eq151494 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq122082 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122082
  have eq151495 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq151494 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151494
  have eq151496 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq151495 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151495
  have eq152891 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq151496 X1 (τ X0)
       grind)
    | exact superpose eq151496 eq19
    | (have j1 := eq151496 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq151496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq153004 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq151496 (σ X1) (σ X0)
       grind)
    | exact superpose eq151496 eq15
    | (have j1 := eq151496 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq151496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151496
  have eq156118 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152891 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152891
    | exact resolve eq152891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152891
  have eq156600 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq156118 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq156118
    | (have j0 := eq156118 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq156118 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156118
  have eq161093 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq153004 x y
       grind)
    | exact superpose eq153004 eq16
    | (have j1 := eq153004 x y
       grind)
    | exact resolve eq16 eq153004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153004
  have eq162475 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq161093
       have i₂ := eq156600 x y
       grind)
    | exact superpose eq156600 eq161093
    | (have j1 := eq156600 (σ x) (σ y)
       grind)
    | (have r₁ := eq161093
       have r₂ := eq156600 x y
       grind)
    | (have r₁ := eq161093
       have r₂ := eq156600 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq161093
       have r₂ := eq156600 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq161093 eq156600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156600 eq161093
  have eq162482 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq162475
  have eq162486 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq162482
       grind)
    | exact superpose eq162482 eq16
    | exact resolve eq16 eq162482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162482
  have eq162487 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq162486
       have r₂ := eq821 x
       grind)
    | exact resolve eq162486 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162486
  have eq163762 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq162487
       grind)
    | exact superpose eq162487 eq16
    | exact resolve eq16 eq162487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163763 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq162487
       grind)
    | exact superpose eq162487 eq10
    | exact resolve eq10 eq162487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162487
  have eq164032 : x = y := by
    first
    | (have i₁ := eq163763
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq163763
    | exact resolve eq163763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163763
  have eq164033 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq163762
       have i₂ := eq821 x
       grind)
    | exact superpose eq821 eq163762
    | exact resolve eq163762 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq163762
  have eq164048 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq164033
       have i₂ := eq164032
       grind)
    | exact superpose eq164032 eq164033
    | exact resolve eq164033 eq164032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164032 eq164033
  have eq164049 : False := by grind
  exact eq164049

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 ∨ (M.op (M.op (M.op X1 X1) (M.op X0 X0)) X0) = (M.op (M.op (M.op X1 X1) (M.op X0 X0)) (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X0)) X0) = (M.op (M.op (M.op X1 X1) (M.op X0 X0)) (M.op (M.op X1 X1) (M.op X0 X0))) ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq100 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq177 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq90
    | exact resolve eq90 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq209 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq215 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq209 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq209 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq209 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq270 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) ≠ (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) ∨ (k X2 (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (k X1 (M.op (M.op X0 X0) (M.op X1 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 X0) (M.op X1 X1))
       have j1 := eq57 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq215 (σ X0) X1
       grind)
    | exact superpose eq215 eq15
    | (have j1 := eq215 (σ X0) X1
       grind)
    | exact resolve eq15 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1535 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (M.op (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq178 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1537 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (M.op (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1535 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1539 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (M.op (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1537 X0 X1 X2
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq1537
    | (have j0 := eq1537 X0 X1 X2
       grind)
    | exact resolve eq1537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1537
  have eq1555 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1539 X0 X1 X2
       have i₂ := eq40 X2
       grind)
    | exact superpose eq40 eq1539
    | (have j0 := eq1539 X0 X1 X2
       grind)
    | exact resolve eq1539 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1539
  have eq1556 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1555 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq2252 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq270 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq2256 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2252 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq2252
    | (have j0 := eq2252 X0 X1
       grind)
    | exact resolve eq2252 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq2257 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2256 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq2286 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 X1) (M.op (τ X0) (τ X0)))
       have i₂ := eq2257 (τ X0) X1
       grind)
    | exact superpose eq2257 eq17
    | exact resolve eq17 eq2257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq2297 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2286 X0 X1
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq2286
    | exact resolve eq2286 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq2305 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2297 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2297
    | exact resolve eq2297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq2494 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 X1) (τ (M.op (τ X0) (τ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op X1 X1) (τ (M.op (τ X0) (τ X0)))))
       have i₂ := eq2305 (τ X0) X1
       grind)
    | exact superpose eq2305 eq17
    | exact resolve eq17 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq2511 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 X1) (τ (τ (M.op X0 X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2494 X0 X1
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq2494
    | exact resolve eq2494 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq2540 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op X1 X1) (τ (τ (M.op X0 X0))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2511 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2511
    | exact resolve eq2511 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq3711 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq480 x y
       grind)
    | exact superpose eq480 eq16
    | (have j1 := eq480 x y
       grind)
    | exact resolve eq16 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3827 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq4868 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3827 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq3827
    | (have j0 := eq3827 (τ X0) (τ X1)
       grind)
    | exact resolve eq3827 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq4897 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4868 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4868
    | (have j0 := eq4868 X0 X1
       grind)
    | exact resolve eq4868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868
  have eq4903 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4897 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4897
    | (have j0 := eq4897 X0 X1
       grind)
    | exact resolve eq4897 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4897
  have eq4904 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4903 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4903
    | (have j0 := eq4903 X0 X1
       grind)
    | exact resolve eq4903 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4903
  have eq4905 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4904 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4904
    | (have j0 := eq4904 X0 X1
       grind)
    | exact resolve eq4904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4904
  have eq6295 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2540 (τ X0) X1
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq2540
    | exact resolve eq2540 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6339 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (M.op (τ X0) (τ X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op (M.op X1 X1) (τ (τ (M.op (τ X0) (τ X0)))))))
       have i₂ := eq2540 (τ X0) X1
       grind)
    | exact superpose eq2540 eq17
    | exact resolve eq17 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq6360 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6339 X0 X1
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq6339
    | exact resolve eq6339 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq6339
  have eq6396 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6360 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6360
    | exact resolve eq6360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6360
  have eq38954 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0)))))))))) ∨ (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1556 X0 (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))) X2
       have i₂ := eq6295 X0 X1
       grind)
    | exact superpose eq6295 eq1556
    | (have j0 := eq1556 X0 (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))) X2
       grind)
    | exact resolve eq1556 eq6295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556 eq6295
  have eq39354 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = X0 ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0)))))))))) ∨ (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38954 X0 X1 X2
       have i₂ := eq6396 X0 X1
       grind)
    | exact superpose eq6396 eq38954
    | (have j0 := eq38954 X0 X1 X2
       grind)
    | exact resolve eq38954 eq6396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38954
  have eq39439 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = X0 ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0)))))))))) ∨ (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39354 X0 X1 X2
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq39354
    | (have j0 := eq39354 X0 X1 X2
       grind)
    | exact resolve eq39354 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39354
  have eq39523 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (σ X2) X0) ∨ (k X0 (σ X2)) = X0 ∨ (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39439 X0 X1 X2
       have i₂ := eq6396 X0 X1
       grind)
    | exact superpose eq6396 eq39439
    | (have j0 := eq39439 X0 X1 X2
       grind)
    | exact resolve eq39439 eq6396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39439
  have eq39606 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (σ (k (τ X0) X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) X0) ∨ (k X0 (σ X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq39523 X0 x X2
       have i₂ := eq6396 X0 x
       grind)
    | exact superpose eq6396 eq39523
    | (have j0 := eq39523 X0 x X2
       grind)
    | exact resolve eq39523 eq6396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6396 eq39523
  have eq39682 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) X0) ∨ (k X0 (σ X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq39606 X0 X2
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq39606
    | (have j0 := eq39606 X0 X2
       grind)
    | exact resolve eq39606 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq39606
  have eq39749 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (k X0 (σ X2)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq39682 X0 X2
       have j1 := eq77 X2 X0
       grind)
    | (have r₁ := eq39682 x X0
       have r₂ := eq77 X0 x
       grind)
    | exact resolve eq39682 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq39682
  have eq39915 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39749 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39749
    | exact resolve eq39749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39749
  have eq40354 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3711
       have i₂ := eq39915 y x
       grind)
    | exact superpose eq39915 eq3711
    | (have j1 := eq39915 y x
       grind)
    | exact resolve eq3711 eq39915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3711
  have eq40356 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39915 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39915
  have eq40358 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq40354
  have eq41404 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq40356 (σ x) (σ y)
       have i₂ := eq40358
       grind)
    | exact superpose eq40358 eq40356
    | (have j0 := eq40356 (σ x) (σ y)
       grind)
    | (have r₁ := eq40356 (σ x) (σ y)
       have r₂ := eq40358
       grind)
    | exact resolve eq40356 eq40358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40358
  have eq41408 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq41404
  have eq41412 : x = (k x y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41408
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq41408
    | exact resolve eq41408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41408
  have eq41972 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq3827 x y
       have i₂ := eq41412
       grind)
    | exact superpose eq41412 eq3827
    | (have j0 := eq3827 x y
       grind)
    | (have r₁ := eq3827 x y
       have r₂ := eq41412
       grind)
    | exact resolve eq3827 eq41412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41412
  have eq41979 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq41972
  have eq41987 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3827 x y
       grind)
    | (have r₁ := eq41979
       have r₂ := eq3827 x y
       grind)
    | exact resolve eq41979 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827 eq41979
  have eq41995 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq16
    | exact resolve eq16 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41998 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq40356 (σ x) (σ y)
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq40356
    | (have j0 := eq40356 (σ x) (σ y)
       grind)
    | (have r₁ := eq40356 (σ x) (σ y)
       have r₂ := eq41987
       grind)
    | exact resolve eq40356 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40356 eq41987
  have eq42002 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq41998
  have eq42006 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq42002
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq42002
    | exact resolve eq42002 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42002
  have eq43005 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq42006
       grind)
    | exact superpose eq42006 eq10
    | exact resolve eq10 eq42006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42006
  have eq43144 : x = (k x y) := by
    first
    | (have i₁ := eq43005
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq43005
    | exact resolve eq43005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43005
  have eq43297 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4905 x y
       have i₂ := eq43144
       grind)
    | exact superpose eq43144 eq4905
    | (have j0 := eq4905 x y
       grind)
    | (have r₁ := eq4905 x y
       have r₂ := eq43144
       grind)
    | exact resolve eq4905 eq43144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4905 eq43144
  have eq43302 : x = (M.op x y) := by grind
  clear eq43297
  have eq43311 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq41995
       have i₂ := eq43302
       grind)
    | exact superpose eq43302 eq41995
    | exact resolve eq41995 eq43302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41995 eq43302
  have eq43319 : False := by grind
  exact eq43319
