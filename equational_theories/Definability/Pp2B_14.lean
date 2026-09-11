import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq63 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq137 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq139 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq443 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq105
  have eq445 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq443 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq443
    | (have j0 := eq443 X0
       grind)
    | exact resolve eq443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq446 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq453 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq446 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq446
    | exact resolve eq446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ X0) (σ X0)
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq63
    | exact resolve eq63 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq453 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq453
    | exact resolve eq453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq453
  have eq474 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq473 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq473
    | exact resolve eq473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq581 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq459 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq459 X0 x
       grind)
    | exact superpose eq459 eq459
    | exact resolve eq459 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq607 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq581 X0
       have i₂ := eq474 (k X0 X0)
       grind)
    | exact superpose eq474 eq581
    | exact resolve eq581 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq615 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq607 X0
       have i₂ := eq474 X0
       grind)
    | exact superpose eq474 eq607
    | exact resolve eq607 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq615 X0
       have i₂ := eq63 X0 X0 X0
       grind)
    | (have i₁ := eq615 X0
       have i₂ := eq63 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq63 eq615
    | exact resolve eq615 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq615
  have eq633 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq644 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq633 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq633
    | exact resolve eq633 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq648 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq644
  have eq706 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq137 x y
       grind)
    | exact superpose eq137 eq16
    | (have j1 := eq137 x y
       grind)
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq728 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq706
       have i₂ := eq446 x
       grind)
    | exact superpose eq446 eq706
    | exact resolve eq706 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq706
  have eq739 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq728
       have i₂ := eq474 x
       grind)
    | exact superpose eq474 eq728
    | exact resolve eq728 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq728
  have eq6828 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139
    | exact resolve eq139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq6964 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6828 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6828
    | (have j0 := eq6828 X0 X1
       grind)
    | exact resolve eq6828 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6828
  have eq19032 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq739
       have i₂ := eq6964 y x
       grind)
    | exact superpose eq6964 eq739
    | (have j1 := eq6964 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq739
       have r₂ := eq6964 y x
       grind)
    | (have r₁ := eq739
       have r₂ := eq6964 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq739
       have r₂ := eq6964 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq739 eq6964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq6964
  have eq19033 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq19032
  have eq19035 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19033
       grind)
    | exact superpose eq19033 eq16
    | exact resolve eq16 eq19033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19033
  have eq19036 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19035
       have r₂ := eq621 x
       grind)
    | exact resolve eq19035 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19035
  have eq19038 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19036
       grind)
    | exact superpose eq19036 eq10
    | exact resolve eq10 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036
  have eq19147 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19038
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19038
    | exact resolve eq19038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19038
  have eq19172 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19147
       grind)
    | exact superpose eq19147 eq16
    | exact resolve eq16 eq19147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19147
  have eq19173 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq19172
       have r₂ := eq621 x
       grind)
    | exact resolve eq19172 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq19172
  have eq19190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq648 x
       have i₂ := eq19173
       grind)
    | exact superpose eq19173 eq648
    | exact resolve eq648 eq19173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19173
  have eq19276 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq19190
       have r₂ := eq16
       grind)
    | exact resolve eq19190 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19190
  have eq19307 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq19276
       grind)
    | exact superpose eq19276 eq10
    | exact resolve eq10 eq19276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19276
  have eq19451 : y = (M.op x x) := by
    first
    | (have i₁ := eq19307
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq19307
    | exact resolve eq19307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19307
  have eq19515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq648 x
       have i₂ := eq19451
       grind)
    | exact superpose eq19451 eq648
    | exact resolve eq648 eq19451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq19451
  have eq19601 : False := by grind
  exact eq19601

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq19 X2 X0 x
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq63
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq63
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X0) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq19
    | exact resolve eq19 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) (τ X0) X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq19
    | exact resolve eq19 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq279 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq254
    | (have j0 := eq254 X0 X1
       grind)
    | exact resolve eq254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq254
  have eq283 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq285 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq279
    | (have j0 := eq279 X0 X1
       grind)
    | exact resolve eq279 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq287 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       have j1 := eq108 X1 X0
       grind)
    | (have r₁ := eq283 X0 X0
       have r₂ := eq108 X0 X1
       grind)
    | exact resolve eq283 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq283
  have eq289 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq285 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq285 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq285 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq291 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq287 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq287
    | (have j0 := eq287 X0 X1
       grind)
    | exact resolve eq287 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq960 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq291
    | exact resolve eq291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq960 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq960 X0 X1
       grind)
    | exact superpose eq960 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq960 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq960 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq960 X0 X1
       grind)
    | exact resolve eq13 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1096 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1056 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1108 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1096 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1096 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1096 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1137 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1200 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1137 (σ (M.op X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq104 X0 X1
       grind)
    | exact superpose eq104 eq1137
    | (have j0 := eq1137 (σ (M.op X0 X0)) (M.op (σ X0) X1)
       grind)
    | exact resolve eq1137 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1203 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1137 (τ (M.op X0 X0)) (M.op (τ X0) X1)
       have i₂ := eq164 X0 X1
       grind)
    | exact superpose eq164 eq1137
    | (have j0 := eq1137 (τ (M.op X0 X0)) (M.op (τ X0) X1)
       grind)
    | exact resolve eq1137 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq1137
  have eq1217 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq119 (M.op X0 X0)
       grind)
    | exact superpose eq119 eq1203
    | (have j0 := eq1203 X0 X1
       grind)
    | exact resolve eq1203 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1220 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1200 X0 X1
       have i₂ := eq65 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq1200
    | (have j0 := eq1200 X0 X1
       grind)
    | exact resolve eq1200 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1225 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1217
    | (have j0 := eq1217 X0 X1
       grind)
    | exact resolve eq1217 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1226 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1225 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1228 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1220 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1220 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1220
    | (have j0 := eq1220 X0 X1
       grind)
    | exact resolve eq1220 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1229 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1230 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1226 X0 X1
       have i₂ := eq119 (M.op X0 X0)
       grind)
    | exact superpose eq119 eq1226
    | exact resolve eq1226 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq1226
  have eq1231 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1229 X0 X1
       have i₂ := eq65 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq1229
    | exact resolve eq1229 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1232 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1230 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1230 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1230
    | exact resolve eq1230 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1233 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1231 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1231 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1231
    | exact resolve eq1231 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1253 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X0 X0) (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (M.op X0 X0) (M.op (τ X0) X1)
       have i₂ := eq1232 X0 X1
       grind)
    | exact superpose eq1232 eq17
    | exact resolve eq17 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1232
  have eq1256 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1253 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1253
    | exact resolve eq1253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1381 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq291 (M.op X0 X0) (M.op (τ X0) X1)
       have i₂ := eq1256 X0 X1
       grind)
    | exact superpose eq1256 eq291
    | (have j0 := eq291 (M.op X0 X0) (M.op (τ X0) X1)
       grind)
    | exact resolve eq291 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq1256
  have eq1393 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1381 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1381 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1381
    | (have j0 := eq1381 X0 X1
       grind)
    | exact resolve eq1381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1394 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1524 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1394 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1394
    | exact resolve eq1394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1569 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1524 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq1524
    | exact resolve eq1524 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq1772 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (M.op X0 X0) (M.op (σ X0) X1)
       have i₂ := eq1233 X0 X1
       grind)
    | exact superpose eq1233 eq40
    | exact resolve eq40 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1233
  have eq1775 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1772 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1772
    | exact resolve eq1772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq1802 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (τ (M.op (σ (σ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1775 (σ X0) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq1775
    | exact resolve eq1775 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1775
  have eq1917 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ (M.op X0 X0)) (σ (M.op X0 X1)) X2
       have i₂ := eq1569 X0 X1
       grind)
    | exact superpose eq1569 eq19
    | exact resolve eq19 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq3953 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (τ (M.op (σ (σ X0)) X1))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (τ (M.op (σ (σ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq289 (τ (M.op (σ (σ X0)) X1)) (M.op X0 X0)
       have i₂ := eq1802 X0 X1
       grind)
    | exact superpose eq1802 eq289
    | (have j0 := eq289 (τ (M.op (σ (σ X0)) X1)) (M.op X0 X0)
       grind)
    | exact resolve eq289 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq1802
  have eq3974 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (τ (M.op (σ (σ X0)) X1))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (τ (M.op (σ (σ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3953 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq3953 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq3953
    | (have j0 := eq3953 X0 X1
       grind)
    | exact resolve eq3953 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3953
  have eq3975 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (τ (M.op (σ (σ X0)) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3974 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3974
  have eq4335 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3975 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3975
    | exact resolve eq3975 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3975
  have eq4411 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4335 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq4335
    | exact resolve eq4335 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq4335
  have eq4639 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (τ (M.op (σ X0) X1)) X1 (M.op X0 X0)
       have i₂ := eq4411 X0 X1
       grind)
    | exact superpose eq4411 eq25
    | exact resolve eq25 eq4411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4411
  have eq4715 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4639 (τ X0) X2 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4639
    | exact resolve eq4639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639
  have eq6133 : ∀ X0 X1 X3 : G, (σ (τ X0)) = (M.op (σ (M.op X1 (τ X0))) (M.op (σ (τ X0)) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1917 (M.op X1 (τ X0)) (τ (M.op X0 x)) x
       have i₂ := eq4715 X0 X1 x
       grind)
    | exact superpose eq4715 eq1917
    | exact resolve eq1917 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4715
  have eq6249 : ∀ X0 X1 X3 : G, (M.op (σ (M.op X1 (τ X0))) (M.op X0 X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6133 X0 X1 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6133
    | exact resolve eq6133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6133
  have eq6353 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1917 X1 (τ X0) (M.op X0 x)
       have i₂ := eq6249 X0 X1 x
       grind)
    | exact superpose eq6249 eq1917
    | exact resolve eq1917 eq6249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917 eq6249
  have eq6582 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6353 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6353
    | exact resolve eq6353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6353
  have eq6768 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6582 y x
       grind)
    | exact superpose eq6582 eq16
    | (have r₁ := eq16
       have r₂ := eq6582 y x
       grind)
    | exact resolve eq16 eq6582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq6873 : False := by grind
  exact eq6873

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq63
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq63
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100
    | (have j0 := eq100 (τ X0) X1
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq272 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq247 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq247
    | (have j0 := eq247 X0 X1
       grind)
    | exact resolve eq247 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq247
  have eq278 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       have j1 := eq111 X1 X0
       grind)
    | (have r₁ := eq272 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq111 (M.op (τ X0) (τ X0)) X1
       grind)
    | (have r₁ := eq272 X0 X0
       have r₂ := eq111 X0 X1
       grind)
    | exact resolve eq272 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq272
  have eq282 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq278
    | (have j0 := eq278 X0 X1
       grind)
    | exact resolve eq278 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq925 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq282
    | (have j0 := eq282 X1 (τ X0)
       grind)
    | exact resolve eq282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq282 (σ X0) X1
       grind)
    | exact superpose eq282 eq15
    | (have j1 := eq282 (σ X0) X1
       grind)
    | exact resolve eq15 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq949 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq936 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq936
    | (have j0 := eq936 X0 X1
       grind)
    | exact resolve eq936 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq954 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq925
    | (have j0 := eq925 X0 X1
       grind)
    | exact resolve eq925 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq1014 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1
       have i₂ := eq954 X0 (τ X1)
       grind)
    | (have i₁ := eq68 X0
       have i₂ := eq954 (τ X0) X1
       grind)
    | exact superpose eq954 eq68
    | (have j1 := eq954 X0 (τ X1)
       grind)
    | exact resolve eq68 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq954
  have eq2640 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1014 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1014
    | (have j0 := eq1014 X1 (σ X0)
       grind)
    | exact resolve eq1014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq2673 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2640 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq2640
    | (have j0 := eq2640 X0 X1
       grind)
    | exact resolve eq2640 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640
  have eq3952 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq949 x y
       grind)
    | exact superpose eq949 eq16
    | (have j1 := eq949 x y
       grind)
    | exact resolve eq16 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq4813 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3952
       have i₂ := eq2673 x y
       grind)
    | exact superpose eq2673 eq3952
    | (have j1 := eq2673 x y
       grind)
    | exact resolve eq3952 eq2673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673 eq3952
  have eq4814 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4813
  have eq4815 : (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4814
  have eq5060 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq65 (M.op y y)
       have i₂ := eq4815
       grind)
    | exact superpose eq4815 eq65
    | exact resolve eq65 eq4815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4815
  have eq5114 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq5060
       have i₂ := eq65 (M.op x x)
       grind)
    | exact superpose eq65 eq5060
    | exact resolve eq5060 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5060
  have eq5131 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq5114
       have i₂ := eq19 x x x
       grind)
    | (have i₁ := eq5114
       have i₂ := eq19 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq19 eq5114
    | exact resolve eq5114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5114
  have eq5133 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5131
       have i₂ := eq19 y y y
       grind)
    | (have i₁ := eq5131
       have i₂ := eq19 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq19 eq5131
    | exact resolve eq5131 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5131
  have eq5134 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5133
       grind)
    | exact superpose eq5133 eq16
    | exact resolve eq16 eq5133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5135 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5133
       grind)
    | exact superpose eq5133 eq10
    | exact resolve eq10 eq5133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5133
  have eq5219 : x = y := by
    first
    | (have i₁ := eq5135
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5135
    | exact resolve eq5135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5135
  have eq5220 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5134
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq5134
    | exact resolve eq5134 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq5134
  have eq5222 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5220
       have i₂ := eq5219
       grind)
    | exact superpose eq5219 eq5220
    | exact resolve eq5220 eq5219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5219 eq5220
  have eq5223 : False := by grind
  exact eq5223

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq63
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq63
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0) (τ X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq19
    | exact resolve eq19 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (M.op (σ X0) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq19 X0 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq19
    | (have j1 := eq94 X0 X1
       grind)
    | exact resolve eq19 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq286 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq290 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq295 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq259
    | (have j0 := eq259 X0 X1
       grind)
    | exact resolve eq259 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq259
  have eq300 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq305 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq295 X0 X1
       have j1 := eq105 X1 X0
       grind)
    | (have r₁ := eq295 X0 X0
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq295 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq308 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq300
    | (have j0 := eq300 X0 X1
       grind)
    | exact resolve eq300 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq973 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq305
    | exact resolve eq305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1259 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq309
    | (have j0 := eq309 X1 (τ X0)
       grind)
    | exact resolve eq309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq1325 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1259 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1259
    | (have j0 := eq1259 X0 X1
       grind)
    | exact resolve eq1259 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1341 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1325 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq1325
    | (have j0 := eq1325 X0 X1
       grind)
    | exact resolve eq1325 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1352 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1341 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1341
    | (have j0 := eq1341 X0 X1
       grind)
    | exact resolve eq1341 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1341
  have eq1356 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (M.op X0 X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1352 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq1352
    | (have j0 := eq1352 X0 X1
       grind)
    | exact resolve eq1352 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1352
  have eq1359 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1356 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq1356 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1356 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq1645 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1359 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1359
    | exact resolve eq1359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq1725 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1645 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1850 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1725 (M.op X1 (τ X0)) (τ (M.op X0 X0))
       have i₂ := eq161 X0 X1
       grind)
    | exact superpose eq161 eq1725
    | (have j0 := eq1725 (M.op X1 (τ X0)) (τ (M.op X0 X0))
       grind)
    | exact resolve eq1725 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq1725
  have eq1872 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1850 X0 X1
       have i₂ := eq118 (M.op X0 X0)
       grind)
    | exact superpose eq118 eq1850
    | (have j0 := eq1850 X0 X1
       grind)
    | exact resolve eq1850 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq1883 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1872 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1872 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1872
    | (have j0 := eq1872 X0 X1
       grind)
    | exact resolve eq1872 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq1884 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1896 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1884 X0 X1
       have i₂ := eq118 (M.op X0 X0)
       grind)
    | exact superpose eq118 eq1884
    | exact resolve eq1884 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq1884
  have eq1902 : ∀ X0 X1 : G, (τ X0) = (k (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1896 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1896 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1896
    | exact resolve eq1896 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq1927 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X1 (τ (σ X0))) (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1902 (σ X0) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq1902
    | exact resolve eq1902 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1902
  have eq1939 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X1 (τ (σ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1927 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1927
    | exact resolve eq1927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq1949 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1939 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1939
    | exact resolve eq1939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq2059 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 (M.op (M.op X0 X2) (M.op X0 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq1949 (M.op X0 X2) (M.op x X0)
       have i₂ := eq19 x X0 X2
       grind)
    | exact superpose eq19 eq1949
    | exact resolve eq1949 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq2593 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2059 (σ X1) (σ X0)
       have i₂ := eq279 X1 X0 (σ X1)
       grind)
    | exact superpose eq279 eq2059
    | (have j1 := eq279 X1 X0 x
       grind)
    | exact resolve eq2059 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq2620 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2593 X0 X1
       have j1 := eq105 X0 (σ X1)
       grind)
    | (have r₁ := eq2593 X0 X1
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq2593 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq2593
  have eq2634 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2620 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2620
    | (have j0 := eq2620 X0 X1
       grind)
    | exact resolve eq2620 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620
  have eq2635 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2634 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634
  have eq2731 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2635 y x
       grind)
    | exact superpose eq2635 eq16
    | exact resolve eq16 eq2635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq2866 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2731
       have i₂ := eq973 y x
       grind)
    | exact superpose eq973 eq2731
    | (have j1 := eq973 x y
       grind)
    | exact resolve eq2731 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq2869 : (M.op x y) = (M.op y x) := by grind
  clear eq2866
  have eq2926 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 y x
       have i₂ := eq2869
       grind)
    | exact superpose eq2869 eq19
    | exact resolve eq19 eq2869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2869
  have eq3090 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2059 x y
       have i₂ := eq2926 x
       grind)
    | exact superpose eq2926 eq2059
    | exact resolve eq2059 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq2926
  have eq3248 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2731
       have i₂ := eq3090
       grind)
    | exact superpose eq3090 eq2731
    | exact resolve eq2731 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731 eq3090
  have eq3250 : False := by grind
  exact eq3250

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq63
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq63
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq162 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) (τ X0) X1
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq19
    | exact resolve eq19 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | (have j0 := eq94 X1 X1
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) X2)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X1) (σ X0) X2
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq19 (σ X0) (σ X1) x
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq19
    | (have j1 := eq94 X0 X1
       grind)
    | exact resolve eq19 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq295 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq259
    | (have j0 := eq259 X0 X1
       grind)
    | exact resolve eq259 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq305 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq295 X0 X1
       have j1 := eq105 X1 X0
       grind)
    | (have r₁ := eq295 X0 X0
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq295 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq973 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq305
    | exact resolve eq305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1065 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq973 X1 X0
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq973 X0 X1
       grind)
    | exact superpose eq973 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq973 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq973 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq973 X0 X1
       grind)
    | exact resolve eq13 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1104 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1065 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1119 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1104 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1104 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1104 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1147 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1232 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1147 (M.op (τ X0) X1) (τ (M.op X0 X0))
       have i₂ := eq162 X0 X1
       grind)
    | exact superpose eq162 eq1147
    | (have j0 := eq1147 (M.op (τ X0) X1) (τ (M.op X0 X0))
       grind)
    | exact resolve eq1147 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq1147
  have eq1238 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1232 X0 X1
       have i₂ := eq118 (M.op X0 X0)
       grind)
    | exact superpose eq118 eq1232
    | (have j0 := eq1232 X0 X1
       grind)
    | exact resolve eq1232 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1246 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1238 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1238 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1238
    | (have j0 := eq1238 X0 X1
       grind)
    | exact resolve eq1238 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1247 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1253 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1247 X0 X1
       have i₂ := eq118 (M.op X0 X0)
       grind)
    | exact superpose eq118 eq1247
    | exact resolve eq1247 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq1247
  have eq1257 : ∀ X0 X1 : G, (τ X0) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1253 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1253 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1253
    | exact resolve eq1253 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1273 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1257 (σ X0) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq1257
    | exact resolve eq1257 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1257
  have eq1281 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1273 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1273
    | exact resolve eq1273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1288 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1281 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1281
    | exact resolve eq1281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1412 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1288 (M.op X1 X0) (M.op X0 x)
       have i₂ := eq19 X1 X0 x
       grind)
    | exact superpose eq19 eq1288
    | exact resolve eq1288 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1288
  have eq2116 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1412 (σ X1) (σ X0)
       have i₂ := eq269 X0 X1 (σ X1)
       grind)
    | exact superpose eq269 eq1412
    | (have j1 := eq269 X0 X1 x
       grind)
    | exact resolve eq1412 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq1412
  have eq2174 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2116 X0 X1
       have j1 := eq105 X0 (σ X1)
       grind)
    | (have r₁ := eq2116 X0 X1
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq2116 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq2116
  have eq2185 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2174 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2174
    | (have j0 := eq2174 X0 X1
       grind)
    | exact resolve eq2174 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2186 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185
  have eq2191 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2186 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2186
    | exact resolve eq2186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2208 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2186 x y
       grind)
    | exact superpose eq2186 eq16
    | exact resolve eq16 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2586 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq2191 X0 (τ X1)
       grind)
    | exact superpose eq2191 eq17
    | exact resolve eq17 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2191
  have eq2645 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2586 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2586
    | exact resolve eq2586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586
  have eq2674 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2645 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2645
    | exact resolve eq2645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2817 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2208
       have i₂ := eq2674 x y
       grind)
    | exact superpose eq2674 eq2208
    | exact resolve eq2208 eq2674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208 eq2674
  have eq2818 : False := by grind
  exact eq2818

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq342 (σ X0)
       grind)
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq422 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq61
    | exact resolve eq61 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq430
  have eq796 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq431 X1 (σ X0)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X1 (σ X0)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq836 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq796 (τ X1) X0
       grind)
    | exact superpose eq796 eq18
    | (have j1 := eq796 (τ X1) X0
       grind)
    | exact resolve eq18 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq796
  have eq1318 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq836
    | exact resolve eq836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq1390 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1318 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1318
    | (have j0 := eq1318 X0 X1
       grind)
    | exact resolve eq1318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1901 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq807 x y
       grind)
    | exact superpose eq807 eq16
    | (have j1 := eq807 x y
       grind)
    | exact resolve eq16 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1950 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq807 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq2118 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1901
       have i₂ := eq1390 y x
       grind)
    | exact superpose eq1390 eq1901
    | (have j1 := eq1390 (σ y) (σ x)
       grind)
    | (have r₁ := eq1901
       have r₂ := eq1390 y x
       grind)
    | exact resolve eq1901 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2119 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2118
  have eq2160 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2119
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2119
       grind)
    | exact resolve eq13 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq2171 : x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2160
  have eq70575 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1950 x y
       have i₂ := eq2171
       grind)
    | exact superpose eq2171 eq1950
    | (have j0 := eq1950 x y
       grind)
    | exact resolve eq1950 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950 eq2171
  have eq70585 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq70575
  have eq70586 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq70585
  have eq70596 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70586
       grind)
    | exact superpose eq70586 eq16
    | exact resolve eq16 eq70586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70616 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq70586
       grind)
    | exact superpose eq70586 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq70586
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq70586
       grind)
    | exact resolve eq13 eq70586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70586
  have eq70648 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq70616
  have eq70655 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70648
       have i₂ := eq376 y
       grind)
    | exact superpose eq376 eq70648
    | exact resolve eq70648 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70648
  have eq70671 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70655
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq70655
    | exact resolve eq70655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70655
  have eq132171 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1390 y x
       have i₂ := eq70671
       grind)
    | exact superpose eq70671 eq1390
    | (have j0 := eq1390 y x
       grind)
    | exact resolve eq1390 eq70671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq70671
  have eq132395 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq132171
       have r₂ := eq70596
       grind)
    | exact resolve eq132171 eq70596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132171
  have eq132538 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70596
       have i₂ := eq132395
       grind)
    | exact superpose eq132395 eq70596
    | exact resolve eq70596 eq132395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70596 eq132395
  have eq132586 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq132538
  have eq132587 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq132586
  have eq132630 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq132587
       grind)
    | exact superpose eq132587 eq10
    | exact resolve eq10 eq132587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132587
  have eq132876 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq132630
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq132630
    | exact resolve eq132630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132630
  have eq132877 : y = (M.op y y) := by grind
  clear eq132876
  have eq132931 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq92 y x
       have i₂ := eq132877
       grind)
    | exact superpose eq132877 eq92
    | (have r₁ := eq92 y x
       have r₂ := eq132877
       grind)
    | exact resolve eq92 eq132877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq133045 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq132931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132931
  have eq133225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1901
       have i₂ := eq133045 x
       grind)
    | exact superpose eq133045 eq1901
    | exact resolve eq1901 eq133045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901 eq133045
  have eq133228 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq133225
  have eq133993 : (σ y) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq422 y (σ x)
       have i₂ := eq133228
       grind)
    | exact superpose eq133228 eq422
    | exact resolve eq422 eq133228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq134062 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq133993
       have i₂ := eq132877
       grind)
    | exact superpose eq132877 eq133993
    | exact resolve eq133993 eq132877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132877 eq133993
  have eq134088 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq134062
       have i₂ := eq133228
       grind)
    | exact superpose eq133228 eq134062
    | exact resolve eq134062 eq133228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133228 eq134062
  have eq134126 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq134088
       grind)
    | exact superpose eq134088 eq10
    | exact resolve eq10 eq134088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134088
  have eq134371 : x = y := by
    first
    | (have i₁ := eq134126
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq134126
    | exact resolve eq134126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134126
  have eq134520 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134371
       grind)
    | exact superpose eq134371 eq16
    | exact resolve eq16 eq134371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134371
  have eq134599 : False := by grind
  exact eq134599

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq46 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq35 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq35
    | exact resolve eq35 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq76 y x
       grind)
    | exact superpose eq76 eq73
    | (have j1 := eq76 y x
       grind)
    | exact resolve eq73 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq103 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq76 y sF0
       grind)
    | exact superpose eq76 eq75
    | (have j1 := eq76 y (M.op x y)
       grind)
    | exact resolve eq75 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq128 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq138 : ∀ X0 : G, (σ (k (k (M.op x y) x) X0)) = (k (k (σ (M.op x y)) (σ x)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq128 eq10
    | exact resolve eq10 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq243 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq92 X0 X0
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq92 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq92 X1 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq629 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq615 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq615 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq615 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq76
    | (have j0 := eq76 (σ y) (σ x)
       grind)
    | exact resolve eq76 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq917
    | exact resolve eq917 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq921 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq918
       have r₂ := eq27
       grind)
    | exact resolve eq918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq923 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq921 eq244
    | exact resolve eq244 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq929 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq921 eq51
    | exact resolve eq51 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1053 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq923 eq929
    | exact resolve eq929 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq929
  have eq1071 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1053
  have eq1074 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1071 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1071
       grind)
    | exact resolve eq13 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1349 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1087 eq60
    | exact resolve eq60 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1350 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1087 eq86
    | exact resolve eq86 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1087
  have eq1364 : (τ (σ y)) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq921 eq1349
    | exact resolve eq1349 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq1349
  have eq1374 : (τ (σ y)) = (k x y) ∨ y = (M.op y x) := by grind
  clear eq1364
  have eq1376 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1374
    | exact resolve eq1374 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq8387 : (τ (σ y)) = (k y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1071 eq1350
    | exact resolve eq1350 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq1350
  have eq8418 : (τ (σ y)) = (k y y) ∨ y = (M.op y x) := by grind
  clear eq8387
  have eq8420 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq8418
    | exact resolve eq8418 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8418
  have eq8449 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76 y y
       have i₂ := eq8420
       grind)
    | exact superpose eq8420 eq76
    | (have j0 := eq76 y y
       grind)
    | exact resolve eq76 eq8420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8420
  have eq8450 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq8449
  have eq8613 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq8450
       grind)
    | exact superpose eq8450 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq8450
       grind)
    | exact resolve eq13 eq8450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8450
  have eq8628 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq8613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8613
  have eq8876 : y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1376
       have i₂ := eq8628 x
       grind)
    | exact superpose eq8628 eq1376
    | exact resolve eq1376 eq8628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376 eq8628
  have eq8918 : y = (M.op y x) := by grind
  clear eq8876
  have eq8944 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq243 x
       have i₂ := eq8918
       grind)
    | exact superpose eq8918 eq243
    | exact resolve eq243 eq8918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq8952 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq252 y
       have i₂ := eq8918
       grind)
    | exact superpose eq8918 eq252
    | exact resolve eq252 eq8918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq8983 : y = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq8944 eq208
    | exact resolve eq208 eq8944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq9009 : y = (M.op y y) := by
    first
    | exact superpose eq8944 eq8983
    | exact resolve eq8983 eq8944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8983
  have eq9219 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq9009
       grind)
    | exact superpose eq9009 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq9009
       grind)
    | exact resolve eq13 eq9009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9234 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq9219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9219
  have eq9914 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq129
       have i₂ := eq9234 sF0
       grind)
    | exact superpose eq9234 eq129
    | exact resolve eq129 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9921 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq629 y X0
       have i₂ := eq9234 y
       grind)
    | exact superpose eq9234 eq629
    | (have j0 := eq629 y X0
       grind)
    | exact resolve eq629 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629 eq9234
  have eq9956 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq9921 X0
       have i₂ := eq9009
       grind)
    | exact superpose eq9009 eq9921
    | (have j0 := eq9921 X0
       grind)
    | exact resolve eq9921 eq9009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9009 eq9921
  have eq9957 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq9956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9956
  have eq9958 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq8952 eq9914
    | exact resolve eq9914 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914
  have eq9967 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq9957 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9957
    | (have j0 := eq9957 X0
       grind)
    | exact resolve eq9957 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9957
  have eq9968 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq9958
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9958
    | exact resolve eq9958 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9958
  have eq10147 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9968 eq9967
    | exact resolve eq9967 eq9968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9967
  have eq10249 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq10147 eq52
    | exact resolve eq52 eq10147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq25406 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq8944 eq103
    | exact resolve eq103 eq8944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq8944
  have eq25407 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq25406
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25406
    | exact resolve eq25406 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25406
  have eq25408 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq8952 eq25407
    | exact resolve eq25407 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8952 eq25407
  have eq25421 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq25408 eq76
    | (have j0 := eq76 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq76 eq25408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq25408
  have eq25439 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10147 eq25421
    | exact resolve eq25421 eq10147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10147 eq25421
  have eq25520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq25439 eq10249
    | exact resolve eq10249 eq25439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10249 eq25439
  have eq25559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq25520
    | exact resolve eq25520 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25520
  have eq25562 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq25559
       have r₂ := eq27
       grind)
    | exact resolve eq25559 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25559
  have eq25565 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq25562 eq29
    | exact resolve eq29 eq25562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25562
  have eq25809 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq25565
    | exact resolve eq25565 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25565
  have eq25810 : x = y := by grind
  clear eq25809
  have eq25827 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25810
       grind)
    | exact superpose eq25810 eq18
    | exact resolve eq18 eq25810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25828 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq25810
       grind)
    | exact superpose eq25810 eq24
    | exact resolve eq24 eq25810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq25841 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq25810
       grind)
    | exact superpose eq25810 eq129
    | exact resolve eq129 eq25810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq25930 : x = (M.op x x) := by
    first
    | (have i₁ := eq8918
       have i₂ := eq25810
       grind)
    | exact superpose eq25810 eq8918
    | exact resolve eq8918 eq25810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8918 eq25810
  have eq26030 : (σ x) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq9968 eq25841
    | exact resolve eq25841 eq9968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9968 eq25841
  have eq26043 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25828
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25828
    | exact resolve eq25828 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25828
  have eq26057 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq128 eq26030
    | exact resolve eq26030 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq26030
  have eq26062 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26043 eq26
    | exact resolve eq26 eq26043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq26043
  have eq26420 : x = (M.op x y) := by
    first
    | (have i₁ := eq25930
       have i₂ := eq25827
       grind)
    | exact superpose eq25827 eq25930
    | exact resolve eq25930 eq25827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25827 eq25930
  have eq26421 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq26420 eq20
    | exact resolve eq20 eq26420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26576 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq26421
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26421
    | exact resolve eq26421 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26421
  have eq27138 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26576 eq26057
    | exact resolve eq26057 eq26576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26057
  have eq27145 : ∀ X0 : G, (σ (k (k (M.op x y) x) X0)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq26576 eq138
    | exact resolve eq138 eq26576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq27146 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq26420 eq27145
    | exact resolve eq27145 eq26420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27145
  have eq27184 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (k (k x x) X0)) := by
    intro X0
    first
    | exact superpose eq27138 eq27146
    | exact resolve eq27146 eq27138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27146
  have eq27185 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k (k x x) X0)) := by
    intro X0
    first
    | exact superpose eq37 eq27184
    | exact resolve eq27184 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq27184
  have eq27186 : ∀ X0 : G, (σ (k x X0)) = (σ (k (k x x) X0)) := by
    intro X0
    first
    | exact superpose eq26420 eq27185
    | exact resolve eq27185 eq26420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26420 eq27185
  have eq27187 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26576 eq26062
    | exact resolve eq26062 eq26576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26062
  have eq27209 : (σ (k x x)) ≠ (σ (k x (k x x))) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ (k x x))) := by
    first
    | (have i₁ := eq627 (k x x)
       have i₂ := eq27186 (k x x)
       grind)
    | exact superpose eq27186 eq627
    | (have j0 := eq627 (k x x)
       grind)
    | exact resolve eq627 eq27186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq27186
  have eq27326 : (σ (k x x)) ≠ (k (σ x) (k (σ x) (σ x))) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ (k x x))) := by
    first
    | (have i₁ := eq27209
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq27209
    | exact resolve eq27209 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq27209
  have eq27366 : (σ (k x x)) ≠ (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ (k x x))) := by
    first
    | exact superpose eq26576 eq27326
    | exact resolve eq27326 eq26576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27326
  have eq27396 : (σ (k x x)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ (k x x))) := by
    first
    | exact superpose eq27138 eq27366
    | exact resolve eq27366 eq27138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27366
  have eq27414 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ (k x x))) := by
    first
    | exact superpose eq27138 eq27396
    | exact resolve eq27396 eq27138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27396
  have eq27428 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ (k x x))) := by
    first
    | (have i₁ := eq27414
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq27414
    | exact resolve eq27414 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27414
  have eq27440 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (k x x)) = (M.op (σ (k x x)) (σ (k x x))) := by
    first
    | exact superpose eq26576 eq27428
    | exact resolve eq27428 eq26576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27428
  have eq27446 : (σ (k x x)) = (M.op (σ (k x x)) (σ (k x x))) := by
    first
    | (have r₁ := eq27440
       have r₂ := eq27138
       grind)
    | exact resolve eq27440 eq27138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27440
  have eq27449 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq27446
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq27446
    | exact resolve eq27446 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq27446
  have eq27452 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26576 eq27449
    | exact resolve eq27449 eq26576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26576 eq27449
  have eq27454 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27138 eq27452
    | exact resolve eq27452 eq27138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27138 eq27452
  have eq27621 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27454 eq27187
    | exact resolve eq27187 eq27454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27187 eq27454
  have eq27622 : False := by grind
  exact eq27622

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq342 (σ X0)
       grind)
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq422 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq61
    | exact resolve eq61 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1061 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq431 X1 (σ X0)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X1 (σ X0)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1112 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1061 X1 (τ X0)
       grind)
    | exact superpose eq1061 eq17
    | (have j1 := eq1061 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1061
  have eq1314 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1112 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1112
    | exact resolve eq1112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1314 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1314
    | (have j0 := eq1314 X0 X1
       grind)
    | exact resolve eq1314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1888 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1072 x y
       grind)
    | exact superpose eq1072 eq16
    | (have j1 := eq1072 x y
       grind)
    | exact resolve eq16 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq2098 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq1382 x y
       grind)
    | exact superpose eq1382 eq1888
    | (have j1 := eq1382 (σ x) (σ y)
       grind)
    | (have r₁ := eq1888
       have r₂ := eq1382 x y
       grind)
    | exact resolve eq1888 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq2099 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2098
  have eq2105 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq61
    | exact resolve eq61 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2176 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2105 (M.op y x)
       have i₂ := eq2105 x
       grind)
    | exact superpose eq2105 eq2105
    | exact resolve eq2105 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2191 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2176
  have eq2193 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2191
       grind)
    | exact superpose eq2191 eq16
    | exact resolve eq16 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2195 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq422 y (σ x)
       have i₂ := eq2191
       grind)
    | exact superpose eq2191 eq422
    | exact resolve eq422 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq2200 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq2191
       grind)
    | exact superpose eq2191 eq61
    | exact resolve eq61 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2191
  have eq2341 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2200 (σ (M.op y y))
       have i₂ := eq2195
       grind)
    | exact superpose eq2195 eq2200
    | exact resolve eq2200 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195 eq2200
  have eq2359 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2341
  have eq2362 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2359
       have i₂ := eq376 y
       grind)
    | exact superpose eq376 eq2359
    | exact resolve eq2359 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2359
  have eq2374 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq430 y X0
       have i₂ := eq2362
       grind)
    | exact superpose eq2362 eq430
    | (have j0 := eq430 y X0
       grind)
    | (have r₁ := eq430 y x
       have r₂ := eq2362
       grind)
    | exact resolve eq430 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2402 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq2374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq2405 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2402 X0
       have j1 := eq430 y X0
       grind)
    | (have r₁ := eq2402 X0
       have r₂ := eq430 y x
       grind)
    | exact resolve eq2402 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq2402
  have eq2418 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq2405 (σ X0)
       grind)
    | exact superpose eq2405 eq15
    | exact resolve eq15 eq2405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2545 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2418 x
       grind)
    | exact superpose eq2418 eq16
    | exact resolve eq16 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2644 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2545
       have i₂ := eq1382 x y
       grind)
    | exact superpose eq1382 eq2545
    | (have j1 := eq1382 x y
       grind)
    | (have r₁ := eq2545
       have r₂ := eq1382 x y
       grind)
    | exact resolve eq2545 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq2645 : y = (M.op x y) := by grind
  clear eq2644
  have eq2648 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2193
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq2193
    | exact resolve eq2193 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193 eq2645
  have eq2666 : y = (M.op y y) := by grind
  clear eq2648
  have eq2671 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq92 y x
       have i₂ := eq2666
       grind)
    | exact superpose eq2666 eq92
    | (have r₁ := eq92 y x
       have r₂ := eq2666
       grind)
    | exact resolve eq92 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2666
  have eq2706 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq2671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2808 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2545
       have i₂ := eq2706 x
       grind)
    | exact superpose eq2706 eq2545
    | exact resolve eq2545 eq2706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545 eq2706
  have eq2811 : False := by grind
  exact eq2811
