import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation255`: `x = ((x ◇ x) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation255 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law255 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law255.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq33 (σ X1) (σ X0)
       grind)
    | exact superpose eq33 eq15
    | (have j1 := eq33 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq19
    | (have j1 := eq33 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq33
  have eq185 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq207 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq185
    | (have j0 := eq185 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq185 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq569 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq711 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq569
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq569
    | (have j1 := eq207 (σ x) (σ y)
       grind)
    | (have r₁ := eq569
       have r₂ := eq207 x y
       grind)
    | (have r₁ := eq569
       have r₂ := eq207 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq569
       have r₂ := eq207 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq569 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq569
  have eq712 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq711
  have eq812 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq712
       grind)
    | exact superpose eq712 eq10
    | exact resolve eq10 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq848 : x = y ∨ x = y := by
    first
    | (have i₁ := eq812
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq812
    | exact resolve eq812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq849 : x = y := by grind
  clear eq848
  have eq1023 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq16
    | exact resolve eq16 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq1024 : False := by grind
  exact eq1024

/-- `Equation255`: `x = ((x ◇ x) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation255 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law255 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law255.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq104 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq104 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq104 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq175 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq107 (σ X1) (σ X0)
       grind)
    | exact superpose eq107 eq15
    | (have j1 := eq107 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq107 X1 (τ X0)
       grind)
    | exact superpose eq107 eq19
    | (have j1 := eq107 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq107
  have eq814 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178
    | exact resolve eq178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq854 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq814
    | (have j0 := eq814 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq2091 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175 x y
       grind)
    | exact superpose eq175 eq16
    | (have j1 := eq175 x y
       grind)
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2141 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2091
       have i₂ := eq854 x y
       grind)
    | exact superpose eq854 eq2091
    | (have j1 := eq854 (σ x) (σ y)
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 x y
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2091 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq2091
  have eq2142 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2141
  have eq2212 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2142
       grind)
    | exact superpose eq2142 eq10
    | exact resolve eq10 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq2259 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2212
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2212
    | exact resolve eq2212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq2260 : x = y := by grind
  clear eq2259
  have eq2290 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2260
       grind)
    | exact superpose eq2260 eq16
    | exact resolve eq16 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2291 : False := by grind
  exact eq2291

/-- `Equation255`: `x = ((x ◇ x) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_Equation255 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law255 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law255.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq30
    | (have j0 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq43 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq116 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq144 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq256 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq39 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq10
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq10 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq268 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq256
    | (have j0 := eq256 X0 X1
       grind)
    | exact resolve eq256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1024 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq116 (σ X0) (σ X1)
       grind)
    | exact superpose eq116 eq15
    | (have j1 := eq116 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1024 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1024
    | (have j0 := eq1024 X0 X1
       grind)
    | exact resolve eq1024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1203 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1348 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq268 x y
       grind)
    | exact superpose eq268 eq16
    | (have j1 := eq268 x y
       grind)
    | exact resolve eq16 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq1543 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43
    | exact resolve eq43 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1716 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1543 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1543
    | (have j0 := eq1543 X0 X1
       grind)
    | exact resolve eq1543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1771 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq68
    | (have j0 := eq68 X1 (σ X0)
       grind)
    | (have r₁ := eq68 X0 (σ X0)
       have r₂ := eq23 X0
       grind)
    | exact resolve eq68 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1795 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1771 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1771
    | (have j0 := eq1771 X0 X1
       grind)
    | exact resolve eq1771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq28823 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1348
       have i₂ := eq1716 y x
       grind)
    | exact superpose eq1716 eq1348
    | (have j1 := eq1716 x y
       grind)
    | (have r₁ := eq1348
       have r₂ := eq1716 y x
       grind)
    | (have r₁ := eq1348
       have r₂ := eq1716 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1348
       have r₂ := eq1716 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1348 eq1716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348 eq1716
  have eq28824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq28823
  have eq28825 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq28824
  have eq28921 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq28825
       grind)
    | exact superpose eq28825 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq28825
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq28825
       grind)
    | exact resolve eq12 eq28825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29027 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1795 y X0
       have i₂ := eq28825
       grind)
    | exact superpose eq28825 eq1795
    | (have j0 := eq1795 X0 x
       grind)
    | exact resolve eq1795 eq28825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795 eq28825
  have eq69305 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq28921 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28921
  have eq69417 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq116 x y
       have i₂ := eq69305
       grind)
    | exact superpose eq69305 eq116
    | (have j0 := eq116 x y
       grind)
    | exact resolve eq116 eq69305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq69305
  have eq69426 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq69417
  have eq69432 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1203 x y
       grind)
    | (have r₁ := eq69426
       have r₂ := eq1203 x y
       grind)
    | (have r₁ := eq69426
       have r₂ := eq1203 y x
       grind)
    | exact resolve eq69426 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69426
  have eq94675 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1057 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq106389 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94675 (τ X1) (τ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq94675
    | (have j0 := eq94675 (τ X0) (τ X1)
       grind)
    | exact resolve eq94675 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq94675
  have eq106407 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106389 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq106389
    | (have j0 := eq106389 X0 X1
       grind)
    | exact resolve eq106389 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq106389
  have eq106415 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106407 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq106407
    | (have j0 := eq106407 X0 X1
       grind)
    | exact resolve eq106407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106407
  have eq106421 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106415 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq106415
    | (have j0 := eq106415 X0 X1
       grind)
    | (have r₁ := eq106415 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq106415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106415
  have eq106425 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106421 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq106421
    | (have j0 := eq106421 X0 X1
       grind)
    | exact resolve eq106421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106421
  have eq106427 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106425 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq106425
    | (have j0 := eq106425 X0 X1
       grind)
    | exact resolve eq106425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106425
  have eq106429 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106427 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq106427
    | (have j0 := eq106427 X0 X1
       grind)
    | exact resolve eq106427 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106427
  have eq106431 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq106429 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq106429
    | (have j0 := eq106429 X0 X1
       grind)
    | exact resolve eq106429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106429
  have eq106433 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106431 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq106431
    | (have j0 := eq106431 X0 X1
       grind)
    | exact resolve eq106431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106431
  have eq106437 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106433 X0 X1
       have i₂ := eq144 X0 X1
       grind)
    | exact superpose eq144 eq106433
    | (have j0 := eq106433 X1 X0
       have j1 := eq144 X1 X0
       grind)
    | (have r₁ := eq106433 X0 X1
       have r₂ := eq144 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq106433 X0 X1
       have r₂ := eq144 (k X1 X0) (k X0 X1)
       grind)
    | exact resolve eq106433 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq106433
  have eq106519 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq106437 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106437
  have eq106528 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq106519 X0 X1
       have j1 := eq1203 X1 X0
       grind)
    | (have r₁ := eq106519 X0 X1
       have r₂ := eq1203 X0 X1
       grind)
    | (have r₁ := eq106519 X0 X1
       have r₂ := eq1203 (k X0 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq106519 X0 X1
       have r₂ := eq1203 (M.op X0 X1) (k X0 X1)
       grind)
    | exact resolve eq106519 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq106519
  have eq106552 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq106528 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq106528
    | (have j0 := eq106528 (σ X0) (σ X1)
       grind)
    | exact resolve eq106528 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106528
  have eq106584 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq106552 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq106552
    | (have j0 := eq106552 X0 X1
       grind)
    | exact resolve eq106552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106552
  have eq136541 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq29027 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29027
  have eq136572 : (σ (k y x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq106584 y x
       have i₂ := eq136541
       grind)
    | exact superpose eq136541 eq106584
    | (have j0 := eq106584 y x
       grind)
    | (have r₁ := eq106584 y x
       have r₂ := eq136541
       grind)
    | exact resolve eq106584 eq136541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106584 eq136541
  have eq136577 : (σ (k y x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq136572
  have eq136578 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq136577
  have eq136617 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq136578
       grind)
    | exact superpose eq136578 eq16
    | exact resolve eq16 eq136578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136578
  have eq136668 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq136617
       have i₂ := eq69432
       grind)
    | exact superpose eq69432 eq136617
    | exact resolve eq136617 eq69432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69432 eq136617
  have eq136687 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq136668
  have eq136688 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq136687
  have eq136694 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq136688
       grind)
    | exact superpose eq136688 eq10
    | exact resolve eq10 eq136688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136688
  have eq137137 : x = y ∨ x = y := by
    first
    | (have i₁ := eq136694
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq136694
    | exact resolve eq136694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136694
  have eq137138 : x = y := by grind
  clear eq137137
  have eq137144 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq137138
       grind)
    | exact superpose eq137138 eq16
    | exact resolve eq16 eq137138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137138
  have eq137145 : False := by grind
  exact eq137145

/-- `Equation255`: `x = ((x ◇ x) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation255 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law255 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law255.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq84 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq16
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq391 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq90
    | (have j0 := eq90 (τ X0) (τ X1)
       grind)
    | exact resolve eq90 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq391
    | (have j0 := eq391 X0 X1
       grind)
    | exact resolve eq391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq401 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq398 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq398
    | (have j0 := eq398 X0 X1
       grind)
    | exact resolve eq398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq403 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq401
    | (have j0 := eq401 X0 X1
       grind)
    | exact resolve eq401 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq404 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq403
    | (have j0 := eq403 X0 X1
       grind)
    | exact resolve eq403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq405 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq404
    | (have j0 := eq404 X0 X1
       grind)
    | exact resolve eq404 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq406 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq456 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq91
    | (have j0 := eq91 (τ X0) (τ X1)
       grind)
    | exact resolve eq91 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq464 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq456
    | (have j0 := eq456 X0 X1
       grind)
    | exact resolve eq456 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq467 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq469 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq467
    | (have j0 := eq467 X0 X1
       grind)
    | exact resolve eq467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq470 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq469
    | (have j0 := eq469 X0 X1
       grind)
    | exact resolve eq469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq471 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq470
    | (have j0 := eq470 X0 X1
       grind)
    | exact resolve eq470 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq472 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq471
    | (have j0 := eq471 X0 X1
       grind)
    | exact resolve eq471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq482 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq84
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq483 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq482
  have eq3770 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq483
       grind)
    | exact superpose eq483 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq483
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq483
       grind)
    | exact resolve eq13 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3772 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq483
  have eq3773 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3770
  have eq3774 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3773
       have r₂ := eq3772
       grind)
    | exact resolve eq3773 eq3772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772 eq3773
  have eq3776 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3774
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3774
    | exact resolve eq3774 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq24077 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3776
       grind)
    | exact superpose eq3776 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3776
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3776
       grind)
    | exact resolve eq12 eq3776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq24078 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq24077
  have eq24081 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24078
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq24078
    | exact resolve eq24078 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24078
  have eq24627 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq24081
       grind)
    | exact superpose eq24081 eq10
    | exact resolve eq10 eq24081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24081
  have eq24783 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24627
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq24627
    | exact resolve eq24627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24627
  have eq24786 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq406 x y
       grind)
    | (have r₁ := eq24783
       have r₂ := eq406 x y
       grind)
    | exact resolve eq24783 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq24783
  have eq25061 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq24786
       grind)
    | exact superpose eq24786 eq10
    | exact resolve eq10 eq24786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24786
  have eq25219 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25061
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25061
    | exact resolve eq25061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25061
  have eq25220 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq472 x y
       grind)
    | (have r₁ := eq25219
       have r₂ := eq472 x y
       grind)
    | exact resolve eq25219 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq25219
  have eq25300 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25220
       grind)
    | exact superpose eq25220 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25220
       grind)
    | exact resolve eq13 eq25220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25302 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq25303 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq25300
  have eq25304 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25303
       have r₂ := eq25302
       grind)
    | exact resolve eq25303 eq25302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25303
  have eq25642 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91 x y
       have i₂ := eq25304
       grind)
    | exact superpose eq25304 eq91
    | (have j0 := eq91 x y
       grind)
    | exact resolve eq91 eq25304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq25686 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25642
  have eq132407 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25686
       grind)
    | exact superpose eq25686 eq16
    | exact resolve eq16 eq25686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25686
  have eq132514 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132407
       have i₂ := eq25220
       grind)
    | exact superpose eq25220 eq132407
    | exact resolve eq132407 eq25220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132407
  have eq132517 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq132514
  have eq132518 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq132517
       have r₂ := eq25302
       grind)
    | exact resolve eq132517 eq25302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132517
  have eq132545 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq132518
       grind)
    | exact superpose eq132518 eq16
    | exact resolve eq16 eq132518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132546 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq132518
       grind)
    | exact superpose eq132518 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq132518
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq132518
       grind)
    | exact resolve eq12 eq132518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132518
  have eq132547 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq132546
  have eq132550 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132547
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq132547
    | exact resolve eq132547 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132547
  have eq132572 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132545
       have i₂ := eq25220
       grind)
    | exact superpose eq25220 eq132545
    | exact resolve eq132545 eq25220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25220 eq132545
  have eq132576 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq132572
       have r₂ := eq25302
       grind)
    | exact resolve eq132572 eq25302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25302 eq132572
  have eq132619 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132550
       have i₂ := eq25304
       grind)
    | exact superpose eq25304 eq132550
    | exact resolve eq132550 eq25304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25304
  have eq132657 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq132550
       grind)
    | exact superpose eq132550 eq10
    | exact resolve eq10 eq132550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132550
  have eq132752 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq132619
  have eq132809 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132657
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq132657
    | exact resolve eq132657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132657
  have eq132836 : x = (M.op x y) := by
    first
    | (have r₁ := eq132752
       have r₂ := eq132576
       grind)
    | exact resolve eq132752 eq132576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132576 eq132752
  have eq132837 : y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq132809
       have r₂ := eq12 x y
       grind)
    | exact resolve eq132809 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132809
  have eq132915 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq132837
       grind)
    | exact superpose eq132837 eq90
    | (have j0 := eq90 x y
       grind)
    | exact resolve eq90 eq132837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq132954 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq132915
  have eq134587 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq132954
       grind)
    | exact superpose eq132954 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq132954
       grind)
    | exact resolve eq13 eq132954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134589 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq132954
  have eq134590 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq134587
  have eq134591 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq134590
       have r₂ := eq134589
       grind)
    | exact resolve eq134590 eq134589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134590
  have eq134594 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq134591
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq134591
    | exact resolve eq134591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134591
  have eq134596 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq134594
       have i₂ := eq132837
       grind)
    | exact superpose eq132837 eq134594
    | exact resolve eq134594 eq132837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132837 eq134594
  have eq134597 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq134596
       have r₂ := eq134589
       grind)
    | exact resolve eq134596 eq134589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134589 eq134596
  have eq134662 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134597
       grind)
    | exact superpose eq134597 eq16
    | exact resolve eq16 eq134597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134597
  have eq134666 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq134662
       have i₂ := eq132836
       grind)
    | exact superpose eq132836 eq134662
    | exact resolve eq134662 eq132836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132836 eq134662
  have eq134667 : False := by grind
  exact eq134667

/-- `Equation255`: `x = ((x ◇ x) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation255 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law255 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law255.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq78 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq339 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq368 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq339
    | (have j0 := eq339 X0 X1
       grind)
    | exact resolve eq339 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq748 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq78
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq78 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq748
  have eq4264 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq749
       grind)
    | exact superpose eq749 eq16
    | exact resolve eq16 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4265 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq749
       grind)
    | exact superpose eq749 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq749
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq749
       grind)
    | exact resolve eq13 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq4266 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4265
  have eq4267 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4266
  have eq4269 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4267
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4267
    | exact resolve eq4267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4267
  have eq7943 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq368 x y
       have i₂ := eq4269
       grind)
    | exact superpose eq4269 eq368
    | (have j0 := eq368 x y
       grind)
    | exact resolve eq368 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq7945 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq4269
       grind)
    | exact superpose eq4269 eq10
    | exact resolve eq10 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4269
  have eq7985 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7943
  have eq8012 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7945
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7945
    | exact resolve eq7945 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7945
  have eq8013 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7985
       have r₂ := eq4264
       grind)
    | exact resolve eq7985 eq4264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4264 eq7985
  have eq8016 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq8012
       have r₂ := eq13 y x
       grind)
    | exact resolve eq8012 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8012
  have eq8432 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq80 x y
       have i₂ := eq8016
       grind)
    | exact superpose eq8016 eq80
    | (have j0 := eq80 x y
       grind)
    | exact resolve eq80 eq8016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq8016
  have eq8435 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8432
  have eq8436 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8435
  have eq8622 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8436
       grind)
    | exact superpose eq8436 eq16
    | exact resolve eq16 eq8436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8436
  have eq8850 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8622
       have i₂ := eq8013
       grind)
    | exact superpose eq8013 eq8622
    | exact resolve eq8622 eq8013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8013 eq8622
  have eq8851 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8850
  have eq8852 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8851
  have eq9096 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8852
       grind)
    | exact superpose eq8852 eq10
    | exact resolve eq10 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8852
  have eq9169 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9096
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9096
    | exact resolve eq9096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9096
  have eq9170 : x = y := by grind
  clear eq9169
  have eq9382 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9170
       grind)
    | exact superpose eq9170 eq16
    | exact resolve eq16 eq9170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9170
  have eq9383 : False := by grind
  exact eq9383

/-- `Equation283`: `x = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_x_x_pxy_Equation283 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law283 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law283.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op (M.op X0 X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X0 X0) X0) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X1) X1) X1
       have r₂ := eq9 (M.op (M.op X1 X1) X1) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op X0 X0) X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq19 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq10
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op (M.op X0 X0) X1) = X1 ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq42 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq42 eq15
    | (have j1 := eq42 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq41 X0 X0 X2
       grind)
    | exact superpose eq41 eq9
    | (have j1 := eq41 X0 X1 X2
       grind)
    | exact resolve eq9 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37 x y
       grind)
    | exact superpose eq37 eq16
    | (have j1 := eq37 x x
       grind)
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq37 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq197 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq408 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq197 (M.op (M.op X0 X0) X0)
       have i₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq20 eq197
    | (have j0 := eq197 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq413 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq197 (τ X0)
       have i₂ := eq22 X0 (τ X0)
       grind)
    | exact superpose eq22 eq197
    | (have j0 := eq197 (τ X0)
       grind)
    | exact resolve eq197 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq197
  have eq415 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq408 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq418 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq413 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq413
    | (have j0 := eq413 X0
       grind)
    | exact resolve eq413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq421 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq418 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq418
    | (have j0 := eq418 X0
       grind)
    | exact resolve eq418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq431 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq421 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq421
    | (have j0 := eq421 (τ X0)
       grind)
    | exact resolve eq421 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2018 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq196 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq196
    | (have j0 := eq196 (τ X0) (τ X0)
       grind)
    | exact resolve eq196 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq2043 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2018 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2018
    | (have j0 := eq2018 X0 X0
       grind)
    | exact resolve eq2018 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq2047 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2043 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2043
    | (have j0 := eq2043 X0 X0
       grind)
    | exact resolve eq2043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2050 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2047 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2047
    | (have j0 := eq2047 X0 X1
       grind)
    | exact resolve eq2047 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq2052 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2050 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2050
    | (have j0 := eq2050 X0 X1
       grind)
    | exact resolve eq2050 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050
  have eq2053 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2052 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2052
    | (have j0 := eq2052 X0 X1
       grind)
    | exact resolve eq2052 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2549 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ X0)) X1) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq83 X0 X2 (σ X1)
       grind)
    | exact superpose eq83 eq26
    | (have j1 := eq83 X0 X2 X2
       grind)
    | exact resolve eq26 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2556 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (k (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq83 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2587 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2549 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2549
    | (have j0 := eq2549 X0 X1 X2
       grind)
    | exact resolve eq2549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549
  have eq2776 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq184
       have i₂ := eq42 x X0 y
       grind)
    | exact superpose eq42 eq184
    | (have j1 := eq42 x X0 y
       grind)
    | exact resolve eq184 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq2777 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq184
       have i₂ := eq133 x X0 y
       grind)
    | exact superpose eq133 eq184
    | (have j1 := eq133 (σ x) (σ x) (σ x)
       grind)
    | exact resolve eq184 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq2778 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2777 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq2779 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2776
  have eq14648 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op (M.op X0 X0) X0))
       have i₂ := eq415 X0
       grind)
    | exact superpose eq415 eq9
    | exact resolve eq9 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14673 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14648 X0 X1
       have i₂ := eq415 X0
       grind)
    | exact superpose eq415 eq14648
    | exact resolve eq14648 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14648
  have eq14723 : ∀ X0 X1 : G, (M.op (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14673 (σ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq14673 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq14673 eq14673
    | exact resolve eq14673 eq14673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14728 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14673 X0 X1
       have i₂ := eq41 X0 X0 X2
       grind)
    | exact superpose eq41 eq14673
    | (have j1 := eq41 X0 X1 X2
       grind)
    | exact resolve eq14673 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq14673
  have eq14782 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14723 X0 X1
       have i₂ := eq415 X0
       grind)
    | exact superpose eq415 eq14723
    | exact resolve eq14723 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq14723
  have eq18501 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k x X0) = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq14728 x (σ y) X0
       grind)
    | exact superpose eq14728 eq16
    | (have j1 := eq14728 x x X0
       grind)
    | exact resolve eq16 eq14728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14728
  have eq24983 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2556 (τ X0) (τ X1) X2
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq2556
    | (have j0 := eq2556 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq2556 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2556
  have eq25103 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24983 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq24983
    | (have j0 := eq24983 X0 X1 X2
       grind)
    | exact resolve eq24983 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24983
  have eq25118 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25103 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25103
    | (have j0 := eq25103 X0 X1 X2
       grind)
    | exact resolve eq25103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25103
  have eq25128 : ∀ X0 X1 X2 : G, (k X0 X2) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25118 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25118
    | (have j0 := eq25118 X0 X1 X2
       grind)
    | exact resolve eq25118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25118
  have eq25137 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X2) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25128 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25128
    | (have j0 := eq25128 X0 X1 X2
       grind)
    | exact resolve eq25128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25128
  have eq25142 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (k X0 X2) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25137 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25137
    | (have j0 := eq25137 X0 X1 X2
       grind)
    | exact resolve eq25137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25137
  have eq35096 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k X0 X2) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2587 X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq88168 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2778 X0
       grind)
    | exact superpose eq2778 eq13
    | (have j0 := eq13 (σ x) (σ y)
       have j1 := eq2778 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2778 X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq2778 x
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2778 X0
       grind)
    | exact resolve eq13 eq2778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq88193 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq88168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88168
  have eq88194 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq88193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88193
  have eq88204 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq88194 X0
       have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq88194 X0
       have r₂ := eq12 (σ x) x
       grind)
    | (have r₁ := eq88194 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq88194 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88194
  have eq88212 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq88204 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq88204
    | (have j0 := eq88204 X0
       grind)
    | exact resolve eq88204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88204
  have eq88228 : ∀ X0 : G, (k x y) = (τ (σ x)) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq88212 X0
       grind)
    | exact superpose eq88212 eq10
    | (have j1 := eq88212 X0
       grind)
    | exact resolve eq10 eq88212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88212
  have eq88424 : ∀ X0 : G, x = (k x y) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq88228 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq88228
    | (have j0 := eq88228 X0
       grind)
    | exact resolve eq88228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88228
  have eq88465 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2779 X0
       grind)
    | exact superpose eq2779 eq13
    | (have j0 := eq13 (σ x) (σ y)
       have j1 := eq2779 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2779 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2779 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2779 X0
       grind)
    | exact resolve eq13 eq2779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq88589 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq88465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88465
  have eq88590 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq88589 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88589
  have eq88626 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq88590 X0
       have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq88590 X0
       have r₂ := eq12 (σ x) x
       grind)
    | exact resolve eq88590 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88590
  have eq88632 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq88626 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq88626
    | (have j0 := eq88626 X0
       grind)
    | exact resolve eq88626 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88626
  have eq88641 : ∀ X0 X1 : G, x = (M.op x y) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) ∨ (M.op x X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq133 x X0 y
       have i₂ := eq88424 X1
       grind)
    | exact superpose eq88424 eq133
    | (have j0 := eq133 x X0 y
       have j1 := eq88424 X0
       grind)
    | exact resolve eq133 eq88424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq88645 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2053 x y
       have i₂ := eq88424 X0
       grind)
    | exact superpose eq88424 eq2053
    | (have j0 := eq2053 x x
       have j1 := eq88424 x
       grind)
    | (have r₁ := eq2053 x y
       have r₂ := eq88424 X0
       grind)
    | exact resolve eq2053 eq88424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053 eq88424
  have eq88686 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq88645 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88645
  have eq88687 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq88686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88686
  have eq88691 : ∀ X0 X1 : G, x = (M.op x y) ∨ (M.op x X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq88641 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88641
  have eq90482 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ (M.op x X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 x y
       have i₂ := eq88687 X0
       grind)
    | exact superpose eq88687 eq13
    | (have j0 := eq13 x y
       have j1 := eq88687 x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq88687 X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq88687 x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq88687 X0
       grind)
    | exact resolve eq13 eq88687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88687
  have eq90515 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq90482 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90482
  have eq90516 : ∀ X0 : G, x = (M.op x x) ∨ x = (k x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq90515 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90515
  have eq90524 : ∀ X0 : G, x = (k x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq90516 X0
       have j1 := eq12 x y
       grind)
    | (have r₁ := eq90516 X0
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq90516 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq90516 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90516
  have eq92863 : ∀ X0 : G, X0 ≠ X0 ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq88691 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88691
  have eq92864 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq92863 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92863
  have eq93698 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq96648 : ∀ X0 : G, (k x y) = (τ (σ x)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq88632 X0
       grind)
    | exact superpose eq88632 eq10
    | (have j1 := eq88632 X0
       grind)
    | exact resolve eq10 eq88632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88632
  have eq96967 : ∀ X0 : G, x = (k x y) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq96648 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq96648
    | (have j0 := eq96648 y
       grind)
    | exact resolve eq96648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96648
  have eq96968 : ∀ X0 : G, x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq96967 X0
       have j1 := eq25142 x y X0
       grind)
    | (have r₁ := eq96967 X0
       have r₂ := eq25142 x y x
       grind)
    | (have r₁ := eq96967 x
       have r₂ := eq25142 x x x
       grind)
    | exact resolve eq96967 eq25142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25142 eq96967
  have eq98096 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq431 x
       have i₂ := eq96968 x
       grind)
    | exact superpose eq96968 eq431
    | (have j0 := eq431 x
       grind)
    | exact resolve eq431 eq96968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq96968
  have eq98276 : (τ x) = (M.op (τ x) (τ x)) ∨ x = (M.op x y) := by grind
  clear eq98096
  have eq104957 : ∀ X0 : G, (M.op (M.op (τ x) (τ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (τ x)
       have i₂ := eq98276
       grind)
    | exact superpose eq98276 eq9
    | exact resolve eq9 eq98276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98276
  have eq109459 : ∀ X0 : G, (M.op (σ (σ (τ x))) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14782 (τ x) X0
       have i₂ := eq104957 (τ x)
       grind)
    | exact superpose eq104957 eq14782
    | exact resolve eq14782 eq104957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14782 eq104957
  have eq109573 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq109459 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq109459
    | exact resolve eq109459 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109459
  have eq111854 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109573 (σ y)
       grind)
    | exact superpose eq109573 eq16
    | exact resolve eq16 eq109573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109573
  have eq114103 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111854
       have i₂ := eq92864 y
       grind)
    | exact superpose eq92864 eq111854
    | exact resolve eq111854 eq92864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92864 eq111854
  have eq114104 : x = y ∨ x = (M.op x y) := by grind
  clear eq114103
  have eq114108 : x = (M.op x y) := by
    first
    | (have r₁ := eq114104
       have r₂ := eq93698
       grind)
    | exact resolve eq114104 eq93698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93698 eq114104
  have eq393373 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35096 x y X0
       have i₂ := eq90524 X1
       grind)
    | exact superpose eq90524 eq35096
    | (have j0 := eq35096 x y X0
       have j1 := eq90524 X1
       grind)
    | exact resolve eq35096 eq90524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35096 eq90524
  have eq393399 : ∀ X0 X1 : G, x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq393373 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393373
  have eq396498 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ x = (k x X0) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq393399 X0 X1
       grind)
    | exact superpose eq393399 eq16
    | (have j1 := eq393399 X0 X1
       grind)
    | exact resolve eq16 eq393399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393399
  have eq396524 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ x = (k x X0) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq396498 X0 X1
       have i₂ := eq114108
       grind)
    | exact superpose eq114108 eq396498
    | (have j0 := eq396498 X0 X1
       grind)
    | exact resolve eq396498 eq114108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396498
  have eq396525 : ∀ X0 X1 : G, x = (k x X0) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq396524 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396524
  have eq398067 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq421 x
       have i₂ := eq396525 x X0
       grind)
    | exact superpose eq396525 eq421
    | (have j0 := eq421 x
       have j1 := eq396525 X0 x
       grind)
    | (have r₁ := eq421 x
       have r₂ := eq396525 x x
       grind)
    | exact resolve eq421 eq396525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq396525
  have eq398360 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq398067 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398067
  have eq400067 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq398360 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398360
  have eq400068 : x = (M.op x x) := by grind
  clear eq400067
  have eq401966 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq400068
       grind)
    | exact superpose eq400068 eq9
    | exact resolve eq9 eq400068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401967 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq400068
       grind)
    | exact superpose eq400068 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq400068
       grind)
    | exact resolve eq12 eq400068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402082 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq401967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401967
  have eq402119 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq401966 X0
       have i₂ := eq400068
       grind)
    | exact superpose eq400068 eq401966
    | exact resolve eq401966 eq400068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400068 eq401966
  have eq406481 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k x X0) = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq18501 X0
       have i₂ := eq402119 y
       grind)
    | exact superpose eq402119 eq18501
    | (have j0 := eq18501 X0
       grind)
    | exact resolve eq18501 eq402119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18501
  have eq406486 : x = y := by
    first
    | (have i₁ := eq114108
       have i₂ := eq402119 y
       grind)
    | exact superpose eq402119 eq114108
    | exact resolve eq114108 eq402119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114108
  have eq406488 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq406481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406481
  have eq406491 : ∀ X0 : G, (k x X0) = X0 ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq406488 X0
       have i₂ := eq402119 X0
       grind)
    | exact superpose eq402119 eq406488
    | (have j0 := eq406488 X0
       grind)
    | exact resolve eq406488 eq402119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406488
  have eq406545 : ∀ X0 : G, x = X0 ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq406491 X0
       have i₂ := eq402082 X0
       grind)
    | exact superpose eq402082 eq406491
    | (have j0 := eq406491 X0
       grind)
    | exact resolve eq406491 eq402082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402082 eq406491
  have eq406565 : ∀ X0 : G, x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq406545 X0
       have i₂ := eq402119 X0
       grind)
    | exact superpose eq402119 eq406545
    | (have j0 := eq406545 X0
       grind)
    | exact resolve eq406545 eq402119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402119 eq406545
  have eq406566 : ∀ X0 : G, x = X0 := by
    intro X0
    first
    | (have j0 := eq406565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406565
  have eq408324 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq406486
       grind)
    | exact superpose eq406486 eq16
    | exact resolve eq16 eq406486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406486
  have eq408353 : x ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq408324
       have i₂ := eq406566 (σ (M.op x x))
       grind)
    | exact superpose eq406566 eq408324
    | exact resolve eq408324 eq406566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408324
  have eq408355 : False := by grind
  exact eq408355

/-- `Equation283`: `x = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pxx_pyx_Equation283 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law283 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law283.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) X0) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq43 X0 (M.op X0 X0) X2
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq43 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq52 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq47 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq51 X0 X0 X2
       grind)
    | exact superpose eq51 eq9
    | (have j1 := eq51 X0 X1 X2
       grind)
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq109
    | exact resolve eq109 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq147 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (τ X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq106
    | exact resolve eq106 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq152 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq147 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq147
    | exact resolve eq147 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq147
  have eq210 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq9
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq152 X0
       grind)
    | exact superpose eq152 eq9
    | exact resolve eq9 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq210 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq210
    | exact resolve eq210 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq502 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq118 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq118 eq467
    | exact resolve eq467 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq509 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq502
    | exact resolve eq502 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq637 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq51 X0 X0 X2
       grind)
    | exact superpose eq51 eq509
    | (have j1 := eq51 X0 X1 X2
       grind)
    | exact resolve eq509 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq509
  have eq847 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq358 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq358
    | exact resolve eq358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq894 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq847 X0 X1
       have i₂ := eq152 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq152 eq847
    | exact resolve eq847 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq847
  have eq908 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq894 X0 X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq894
    | exact resolve eq894 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq954 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq68 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq68 eq15
    | (have j1 := eq68 (σ X0) X2 X2
       grind)
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq3350 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (σ (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq637 (τ X0) X2 X1
       grind)
    | exact superpose eq637 eq20
    | (have j1 := eq637 (τ X0) X2 X2
       grind)
    | exact resolve eq20 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq637
  have eq3364 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X2 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3350 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3350
    | (have j0 := eq3350 X0 X1 X2
       grind)
    | exact resolve eq3350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq46832 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3364 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3364
    | (have j0 := eq3364 (σ X0) X1 X2
       grind)
    | exact resolve eq3364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq47389 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46832 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq46832
    | (have j0 := eq46832 X0 X1 X2
       grind)
    | exact resolve eq46832 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46832
  have eq54830 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq954 x y X0
       grind)
    | exact superpose eq954 eq16
    | (have j1 := eq954 x x X0
       grind)
    | exact resolve eq16 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq55265 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq54830 X0
       have j1 := eq47389 x x X0
       grind)
    | (have r₁ := eq54830 X0
       have r₂ := eq47389 x y x
       grind)
    | exact resolve eq54830 eq47389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47389 eq54830
  have eq55514 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq908 (σ x) X0
       have i₂ := eq55265 (σ x)
       grind)
    | exact superpose eq55265 eq908
    | exact resolve eq908 eq55265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq55566 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55265 (σ y)
       grind)
    | exact superpose eq55265 eq16
    | exact resolve eq16 eq55265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55265
  have eq55615 : ∀ X0 : G, (M.op (τ (σ (M.op x x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55514 X0
       have i₂ := eq118 x
       grind)
    | exact superpose eq118 eq55514
    | exact resolve eq55514 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq55514
  have eq55670 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55615 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq55615
    | exact resolve eq55615 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55615
  have eq58820 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq55670 x
       grind)
    | exact superpose eq55670 eq9
    | exact resolve eq9 eq55670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55670
  have eq59765 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq55566
       have i₂ := eq58820 y
       grind)
    | exact superpose eq58820 eq55566
    | exact resolve eq55566 eq58820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55566 eq58820
  have eq59770 : False := by grind
  exact eq59770

/-- `Equation283`: `x = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation283 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law283 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law283.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) X0) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq27 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 X1) X1)
       have r₂ := eq9 (M.op (M.op X1 X1) X1) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq48 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 (M.op (M.op X2 X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X2 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq28 X2 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq72 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 (M.op (M.op X2 X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq126 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq40 X0 X0 X2
       grind)
    | exact superpose eq40 eq9
    | (have j1 := eq40 X0 X1 X2
       grind)
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq207 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (M.op (τ X1) (τ X1)) X2) = X2 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq43 (τ X1) X2 X0
       grind)
    | exact superpose eq43 eq20
    | (have j1 := eq43 (τ X1) X2 X0
       grind)
    | exact resolve eq20 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq43
  have eq302 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq47 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq303 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq302 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq309 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq303 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq303 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq303 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq309 (σ X0)
       grind)
    | exact superpose eq309 eq15
    | exact resolve eq15 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq319 X0
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq319
    | exact resolve eq319 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq426 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq328 X0
       grind)
    | exact superpose eq328 eq9
    | exact resolve eq9 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq328 X0
       grind)
    | exact superpose eq328 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq48 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq48 eq15
    | (have j1 := eq48 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq541 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 X0 X1 X2
       have i₂ := eq328 X0
       grind)
    | exact superpose eq328 eq509
    | (have j0 := eq509 X0 X1 X2
       grind)
    | exact resolve eq509 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq723 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq426 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq426
    | exact resolve eq426 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq751 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq723 X0 X1
       have i₂ := eq328 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq328 eq723
    | exact resolve eq723 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq766 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq751 X0 X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq751
    | exact resolve eq751 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq1705 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) X0) ≠ X0 ∨ (k X0 (M.op (M.op X1 X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1707 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1705 X0 X1
       grind)
    | (have r₁ := eq1705 X0 X1
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq1705 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq1794 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq1707 (τ X0) X1
       grind)
    | exact superpose eq1707 eq19
    | exact resolve eq19 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1707
  have eq1796 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1794 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1794
    | exact resolve eq1794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1876 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (M.op X2 X3) = X3 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq126 X2 X3 X0
       grind)
    | exact superpose eq126 eq9
    | (have j1 := eq126 X2 X3 X0
       grind)
    | exact resolve eq9 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq18181 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (k (σ X2) (σ X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq207
    | (have j0 := eq207 X2 X1 X2
       grind)
    | exact resolve eq207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq18597 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op (M.op X0 X0) X1) = X1 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18181 X0 X1 X2
       have i₂ := eq15 X2 X0
       grind)
    | exact superpose eq15 eq18181
    | (have j0 := eq18181 X0 X1 X2
       grind)
    | exact resolve eq18181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18181
  have eq91695 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq541 X0 X1 X2
       grind)
    | exact superpose eq541 eq10
    | (have j1 := eq541 X0 X1 X2
       grind)
    | exact resolve eq10 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq92506 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91695 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91695
    | (have j0 := eq91695 X0 X1 X2
       grind)
    | exact resolve eq91695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91695
  have eq159149 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = X1 ∨ (M.op X2 X3) = X3 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq766 X0 X1
       have i₂ := eq1876 X0 X0 X2 X3
       grind)
    | exact superpose eq1876 eq766
    | (have j1 := eq1876 X0 X1 X2 X3
       grind)
    | exact resolve eq766 eq1876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq261075 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1796 X1 X0
       have i₂ := eq18597 X0 X0 X2
       grind)
    | exact superpose eq18597 eq1796
    | (have j1 := eq18597 X0 X1 X2
       grind)
    | exact resolve eq1796 eq18597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796 eq18597
  have eq279289 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X0) = (M.op (σ X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq159149 X0 X1 (σ X0) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159149
  have eq279290 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X0) = (M.op (σ X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq279289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279289
  have eq279797 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) x) = (k (σ x) x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq279290 x (σ y)
       grind)
    | exact superpose eq279290 eq16
    | (have j1 := eq279290 x x
       grind)
    | exact resolve eq16 eq279290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279290
  have eq336248 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq92506 x y X0
       grind)
    | exact superpose eq92506 eq16
    | (have j1 := eq92506 x y X0
       grind)
    | exact resolve eq16 eq92506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92506
  have eq337476 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op X0 X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq336248 X0
       have j1 := eq261075 y X0 X0
       grind)
    | (have r₁ := eq336248 X0
       have r₂ := eq261075 y x x
       grind)
    | exact resolve eq336248 eq261075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261075 eq336248
  have eq337490 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq309 (σ y)
       have i₂ := eq337476 (σ y)
       grind)
    | exact superpose eq337476 eq309
    | (have j1 := eq337476 (σ y)
       grind)
    | exact resolve eq309 eq337476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq337476
  have eq337657 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq337490
  have eq337754 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq337657
       have i₂ := eq328 y
       grind)
    | exact superpose eq328 eq337657
    | exact resolve eq337657 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq337657
  have eq337860 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq427 y X0
       have i₂ := eq337754
       grind)
    | exact superpose eq337754 eq427
    | (have j0 := eq427 y X0
       grind)
    | (have r₁ := eq427 y x
       have r₂ := eq337754
       grind)
    | exact resolve eq427 eq337754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337924 : (M.op y y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq337754
       grind)
    | exact superpose eq337754 eq10
    | exact resolve eq10 eq337754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337754
  have eq338006 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq337860 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337860
  have eq338026 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq337924
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq337924
    | exact resolve eq337924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337924
  have eq340056 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq338026
       grind)
    | exact superpose eq338026 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq338026
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq338026
       grind)
    | exact resolve eq12 eq338026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338026
  have eq340363 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq340056 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340056
  have eq370660 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq338006 (σ X0)
       grind)
    | exact superpose eq338006 eq15
    | exact resolve eq15 eq338006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338006
  have eq424224 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq370660 x
       grind)
    | exact superpose eq370660 eq16
    | exact resolve eq16 eq370660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370660
  have eq424813 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq424224
       have i₂ := eq340363 x
       grind)
    | exact superpose eq340363 eq424224
    | exact resolve eq424224 eq340363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340363 eq424224
  have eq424840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq424813
  have eq424841 : x = (M.op x x) := by grind
  clear eq424840
  have eq427723 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq424841
       grind)
    | exact superpose eq424841 eq9
    | exact resolve eq9 eq424841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427779 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq427 x X0
       have i₂ := eq424841
       grind)
    | exact superpose eq424841 eq427
    | (have j0 := eq427 x X0
       grind)
    | exact resolve eq427 eq424841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq427798 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq766 x X0
       have i₂ := eq424841
       grind)
    | exact superpose eq424841 eq766
    | exact resolve eq766 eq424841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq428162 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq427779 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427779
  have eq428379 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq427798 X0
       have i₂ := eq424841
       grind)
    | exact superpose eq424841 eq427798
    | exact resolve eq427798 eq424841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427798
  have eq428402 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq427723 X0
       have i₂ := eq424841
       grind)
    | exact superpose eq424841 eq427723
    | exact resolve eq427723 eq424841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424841 eq427723
  have eq429643 : (σ y) ≠ (σ y) ∨ (M.op (σ x) x) = (k (σ x) x) := by
    first
    | (have i₁ := eq279797
       have i₂ := eq428402 y
       grind)
    | exact superpose eq428402 eq279797
    | exact resolve eq279797 eq428402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279797
  have eq429648 : (M.op (σ x) x) = (k (σ x) x) := by grind
  clear eq429643
  have eq429660 : (M.op (σ x) x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq429648
       have i₂ := eq428162 x
       grind)
    | exact superpose eq428162 eq429648
    | exact resolve eq429648 eq428162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428162 eq429648
  have eq429924 : (σ x) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq429660
       have i₂ := eq428402 (σ x)
       grind)
    | exact superpose eq428402 eq429660
    | exact resolve eq429660 eq428402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429660
  have eq430076 : x = (σ x) := by
    first
    | (have i₁ := eq429924
       have i₂ := eq428379 x
       grind)
    | exact superpose eq428379 eq429924
    | exact resolve eq429924 eq428379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428379 eq429924
  have eq430228 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq430076
       grind)
    | exact superpose eq430076 eq16
    | exact resolve eq16 eq430076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430076
  have eq430612 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq430228
       have i₂ := eq428402 (σ y)
       grind)
    | exact superpose eq428402 eq430228
    | exact resolve eq430228 eq428402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430228
  have eq430730 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq430612
       have i₂ := eq428402 y
       grind)
    | exact superpose eq428402 eq430612
    | exact resolve eq430612 eq428402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428402 eq430612
  have eq430731 : False := by grind
  exact eq430731

/-- `Equation283`: `x = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pyx_Equation283 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law283 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law283.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 X1) X1)
       have r₂ := eq9 (M.op (M.op X1 X1) X1) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq29 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq33 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq21 X1 (τ X0)
       grind)
    | exact superpose eq21 eq24
    | exact resolve eq24 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq34 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq10
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34
    | (have j0 := eq34 X0
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33
    | exact resolve eq33 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X1 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq80 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq121 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    grind
  clear eq39
  have eq127 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq121 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq140 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq16
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq696 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq140 (τ X0)
       have i₂ := eq25 X0 (τ X0)
       grind)
    | exact superpose eq25 eq140
    | (have j0 := eq140 (τ X0)
       grind)
    | exact resolve eq140 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq140
  have eq705 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq696 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq696
    | (have j0 := eq696 X0
       grind)
    | exact resolve eq696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq711 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq705 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq705
    | (have j0 := eq705 X0
       grind)
    | exact resolve eq705 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq725 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq711 (τ X0)
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq711
    | (have j0 := eq711 (τ X0)
       grind)
    | exact resolve eq711 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq711
  have eq1035 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1056 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1035 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1035
    | (have j0 := eq1035 X0
       grind)
    | exact resolve eq1035 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq3494 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k X0 x) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq178
       have i₂ := eq48 x X0 y
       grind)
    | exact superpose eq48 eq178
    | (have j1 := eq48 x X0 y
       grind)
    | (have r₁ := eq178
       have r₂ := eq48 (σ (M.op x y)) x (σ (k y x))
       grind)
    | (have r₁ := eq178
       have r₂ := eq48 (σ (k y x)) x (σ (M.op x y))
       grind)
    | exact resolve eq178 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq178
  have eq3498 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq3494 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3494
  have eq13466 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op (M.op X0 X0) X0))
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq9
    | exact resolve eq9 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13511 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13466 X0 X1
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq13466
    | exact resolve eq13466 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq13466
  have eq35802 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 X0 x
       have i₂ := eq3498 (τ X0)
       grind)
    | exact superpose eq3498 eq24
    | exact resolve eq24 eq3498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3498
  have eq35850 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35802 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35802
    | exact resolve eq35802 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35802
  have eq35872 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq35850 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq35850 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq35850 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35850
  have eq35935 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq725 (σ x)
       have i₂ := eq35872 (σ x)
       grind)
    | exact superpose eq35872 eq725
    | (have j0 := eq725 (σ x)
       grind)
    | exact resolve eq725 eq35872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35872
  have eq36033 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35935
  have eq36081 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq36033
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq36033
    | exact resolve eq36033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36033
  have eq36400 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq36081
       grind)
    | exact superpose eq36081 eq9
    | exact resolve eq9 eq36081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36081
  have eq41365 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq36400 x
       grind)
    | exact superpose eq36400 eq9
    | exact resolve eq9 eq36400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41384 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13511 x X0
       have i₂ := eq36400 x
       grind)
    | exact superpose eq36400 eq13511
    | exact resolve eq13511 eq36400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36400
  have eq43387 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq41384 (σ y)
       grind)
    | exact superpose eq41384 eq16
    | exact resolve eq16 eq41384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41384
  have eq46985 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq43387
       have i₂ := eq41365 y
       grind)
    | exact superpose eq41365 eq43387
    | exact resolve eq43387 eq41365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41365 eq43387
  have eq46986 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq46985
  have eq46987 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq46986
  have eq47654 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq46987
       grind)
    | exact superpose eq46987 eq10
    | exact resolve eq10 eq46987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46987
  have eq47748 : x = y ∨ x = y := by
    first
    | (have i₁ := eq47654
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq47654
    | exact resolve eq47654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47654
  have eq47749 : x = y := by grind
  clear eq47748
  have eq48388 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47749
       grind)
    | exact superpose eq47749 eq16
    | exact resolve eq16 eq47749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47749
  have eq48828 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq48388
       have i₂ := eq29 x
       grind)
    | exact superpose eq29 eq48388
    | (have j1 := eq29 x
       grind)
    | exact resolve eq48388 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq66895 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48828
       have i₂ := eq1056 x
       grind)
    | exact superpose eq1056 eq48828
    | (have j1 := eq1056 (σ x)
       grind)
    | (have r₁ := eq48828
       have r₂ := eq1056 x
       grind)
    | exact resolve eq48828 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq48828
  have eq66897 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq66895
  have eq67870 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq66897
       grind)
    | exact superpose eq66897 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq66897
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq66897
       grind)
    | exact resolve eq12 eq66897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66897
  have eq67917 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq67870 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67870
  have eq69092 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq725 (σ x)
       have i₂ := eq67917 (σ x)
       grind)
    | exact superpose eq67917 eq725
    | (have j0 := eq725 (σ x)
       grind)
    | exact resolve eq725 eq67917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq67917
  have eq69224 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by grind
  clear eq69092
  have eq69280 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69224
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq69224
    | exact resolve eq69224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69224
  have eq69281 : x = (M.op x x) := by grind
  clear eq69280
  have eq70004 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13511 x X0
       have i₂ := eq69281
       grind)
    | exact superpose eq69281 eq13511
    | exact resolve eq13511 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13511
  have eq70022 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq70004 X0
       have i₂ := eq69281
       grind)
    | exact superpose eq69281 eq70004
    | exact resolve eq70004 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70004
  have eq72376 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq48388
       have i₂ := eq70022 (σ x)
       grind)
    | exact superpose eq70022 eq48388
    | exact resolve eq48388 eq70022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48388 eq70022
  have eq72409 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq72376
       have i₂ := eq69281
       grind)
    | exact superpose eq69281 eq72376
    | exact resolve eq72376 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69281 eq72376
  have eq72410 : False := by grind
  exact eq72410

/-- `Equation283`: `x = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation283 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law283 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law283.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq83 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 x y
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq592 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq619 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq592
    | (have j0 := eq592 X0 X1
       grind)
    | exact resolve eq592 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1621 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq83
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq83
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq83
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq83 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1622 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1621
  have eq19900 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1622
       grind)
    | exact superpose eq1622 eq16
    | exact resolve eq16 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19901 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1622
       grind)
    | exact superpose eq1622 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1622
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1622
       grind)
    | exact resolve eq13 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq19902 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq19901
  have eq19903 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq19902
  have eq19905 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19903
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19903
    | exact resolve eq19903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19903
  have eq188223 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq619 x y
       have i₂ := eq19905
       grind)
    | exact superpose eq19905 eq619
    | (have j0 := eq619 x y
       grind)
    | exact resolve eq619 eq19905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq188225 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq19905
       grind)
    | exact superpose eq19905 eq10
    | exact resolve eq10 eq19905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19905
  have eq188341 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq188223
  have eq188379 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq188225
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq188225
    | exact resolve eq188225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188225
  have eq188380 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq188341
       have r₂ := eq19900
       grind)
    | exact resolve eq188341 eq19900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19900 eq188341
  have eq188383 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq188379
       have r₂ := eq13 y x
       grind)
    | exact resolve eq188379 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188379
  have eq189195 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq85 x y
       have i₂ := eq188383
       grind)
    | exact superpose eq188383 eq85
    | (have j0 := eq85 x y
       grind)
    | exact resolve eq85 eq188383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq188383
  have eq189198 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq189195
  have eq189199 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq189198
  have eq189689 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq189199
       grind)
    | exact superpose eq189199 eq16
    | exact resolve eq16 eq189199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189199
  have eq190105 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq189689
       have i₂ := eq188380
       grind)
    | exact superpose eq188380 eq189689
    | exact resolve eq189689 eq188380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188380 eq189689
  have eq190106 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq190105
  have eq190107 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq190106
  have eq190496 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq190107
       grind)
    | exact superpose eq190107 eq10
    | exact resolve eq10 eq190107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190107
  have eq190656 : x = y ∨ x = y := by
    first
    | (have i₁ := eq190496
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq190496
    | exact resolve eq190496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190496
  have eq190657 : x = y := by grind
  clear eq190656
  have eq191155 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190657
       grind)
    | exact superpose eq190657 eq16
    | exact resolve eq16 eq190657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190657
  have eq191156 : False := by grind
  exact eq191156

/-- `Equation283`: `x = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pxy_pyx_Equation283 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law283 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law283.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq53 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X0 X1
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq204 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193
    | (have j0 := eq193 X0 X1
       grind)
    | exact resolve eq193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq250 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq278 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq24 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq24 eq250
    | exact resolve eq250 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq282 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq278
    | exact resolve eq278 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq1049 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X1 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1049 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1049
    | (have j0 := eq1049 (M.op X1 X1) X1
       grind)
    | exact resolve eq1049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq2142 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq204 x y
       grind)
    | exact superpose eq204 eq16
    | (have j1 := eq204 x y
       grind)
    | exact resolve eq16 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq26520 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2142
       have i₂ := eq1113 y x
       grind)
    | exact superpose eq1113 eq2142
    | (have j1 := eq1113 (M.op x x) x
       grind)
    | (have r₁ := eq2142
       have r₂ := eq1113 y x
       grind)
    | (have r₁ := eq2142
       have r₂ := eq1113 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2142
       have r₂ := eq1113 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2142 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113 eq2142
  have eq26521 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26520
  have eq26522 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26521
  have eq26527 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq26522
       grind)
    | exact superpose eq26522 eq9
    | exact resolve eq9 eq26522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26522
  have eq27004 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq26527 x
       grind)
    | exact superpose eq26527 eq9
    | exact resolve eq9 eq26527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27007 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq282 x X0
       have i₂ := eq26527 x
       grind)
    | exact superpose eq26527 eq282
    | exact resolve eq282 eq26527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq26527
  have eq27909 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq27007 (σ y)
       grind)
    | exact superpose eq27007 eq16
    | exact resolve eq16 eq27007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27007
  have eq30349 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27909
       have i₂ := eq27004 y
       grind)
    | exact superpose eq27004 eq27909
    | exact resolve eq27909 eq27004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27004 eq27909
  have eq30350 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30349
  have eq30351 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30350
  have eq30607 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30351
       grind)
    | exact superpose eq30351 eq10
    | exact resolve eq10 eq30351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30351
  have eq30685 : x = y ∨ x = y := by
    first
    | (have i₁ := eq30607
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30607
    | exact resolve eq30607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30607
  have eq30686 : x = y := by grind
  clear eq30685
  have eq30936 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30686
       grind)
    | exact superpose eq30686 eq16
    | exact resolve eq16 eq30686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30686
  have eq30937 : False := by grind
  exact eq30937

/-- `Equation283`: `x = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation283 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law283 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law283.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq53 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X0 X1
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq202 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq248 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq276 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq24 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq24 eq248
    | exact resolve eq248 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq280 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq276
    | exact resolve eq276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq1264 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X1 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1334 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1264
    | (have j0 := eq1264 (M.op X1 X1) X1
       grind)
    | exact resolve eq1264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq2898 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq202 x y
       grind)
    | exact superpose eq202 eq16
    | (have j1 := eq202 x y
       grind)
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq27373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2898
       have i₂ := eq1334 y x
       grind)
    | exact superpose eq1334 eq2898
    | (have j1 := eq1334 (M.op x x) x
       grind)
    | (have r₁ := eq2898
       have r₂ := eq1334 y x
       grind)
    | (have r₁ := eq2898
       have r₂ := eq1334 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2898
       have r₂ := eq1334 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2898 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334 eq2898
  have eq27374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27373
  have eq27375 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27374
  have eq27380 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq27375
       grind)
    | exact superpose eq27375 eq9
    | exact resolve eq9 eq27375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27375
  have eq27867 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq27380 x
       grind)
    | exact superpose eq27380 eq9
    | exact resolve eq9 eq27380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27871 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq280 x X0
       have i₂ := eq27380 x
       grind)
    | exact superpose eq27380 eq280
    | exact resolve eq280 eq27380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq27380
  have eq28726 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq27871 (σ y)
       grind)
    | exact superpose eq27871 eq16
    | exact resolve eq16 eq27871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27871
  have eq31436 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28726
       have i₂ := eq27867 y
       grind)
    | exact superpose eq27867 eq28726
    | exact resolve eq28726 eq27867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27867 eq28726
  have eq31437 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31436
  have eq31438 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq31437
  have eq31782 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq31438
       grind)
    | exact superpose eq31438 eq10
    | exact resolve eq10 eq31438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31438
  have eq31860 : x = y ∨ x = y := by
    first
    | (have i₁ := eq31782
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31782
    | exact resolve eq31782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31782
  have eq31861 : x = y := by grind
  clear eq31860
  have eq32172 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31861
       grind)
    | exact superpose eq31861 eq16
    | exact resolve eq16 eq31861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31861
  have eq32173 : False := by grind
  exact eq32173

/-- `Equation283`: `x = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pyx_Equation283 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law283 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law283.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq53 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X0 X1
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq247 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq236
    | (have j0 := eq236 X0 X1
       grind)
    | exact resolve eq236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq295 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq329 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq24 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq24 eq295
    | exact resolve eq295 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq333 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq329
    | exact resolve eq329 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq1180 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X1 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1180 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1180
    | (have j0 := eq1180 (M.op X1 X1) X1
       grind)
    | exact resolve eq1180 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq3129 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247 x y
       grind)
    | exact superpose eq247 eq16
    | (have j1 := eq247 x y
       grind)
    | exact resolve eq16 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq65030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3129
       have i₂ := eq1251 y x
       grind)
    | exact superpose eq1251 eq3129
    | (have j1 := eq1251 (M.op x x) x
       grind)
    | (have r₁ := eq3129
       have r₂ := eq1251 y x
       grind)
    | (have r₁ := eq3129
       have r₂ := eq1251 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3129
       have r₂ := eq1251 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3129 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq3129
  have eq65031 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65030
  have eq65032 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65031
  have eq65042 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq65032
       grind)
    | exact superpose eq65032 eq9
    | exact resolve eq9 eq65032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65032
  have eq65805 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq65042 x
       grind)
    | exact superpose eq65042 eq9
    | exact resolve eq9 eq65042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65822 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq333 x X0
       have i₂ := eq65042 x
       grind)
    | exact superpose eq65042 eq333
    | exact resolve eq333 eq65042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq65042
  have eq68136 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq65822 (σ y)
       grind)
    | exact superpose eq65822 eq16
    | exact resolve eq16 eq65822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65822
  have eq72160 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68136
       have i₂ := eq65805 y
       grind)
    | exact superpose eq65805 eq68136
    | exact resolve eq68136 eq65805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65805 eq68136
  have eq72161 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq72160
  have eq72162 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq72161
  have eq72655 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq72162
       grind)
    | exact superpose eq72162 eq10
    | exact resolve eq10 eq72162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72162
  have eq72746 : x = y ∨ x = y := by
    first
    | (have i₁ := eq72655
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq72655
    | exact resolve eq72655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72655
  have eq72747 : x = y := by grind
  clear eq72746
  have eq73191 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72747
       grind)
    | exact superpose eq72747 eq16
    | exact resolve eq16 eq72747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72747
  have eq73192 : False := by grind
  exact eq73192

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq96 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq12
    | exact resolve eq12 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq66
    | (have j0 := eq66 (σ X0) (σ X1)
       grind)
    | exact resolve eq66 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq124 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq124 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq124 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq284 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq284 X0 X1
       have j1 := eq134 X0 X1
       grind)
    | (have r₁ := eq284 X0 X1
       have r₂ := eq134 X0 X1
       grind)
    | exact resolve eq284 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq284
  have eq321 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq127 X0 (τ X1)
       grind)
    | exact superpose eq127 eq18
    | (have j1 := eq127 X0 (τ X1)
       grind)
    | exact resolve eq18 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq127
  have eq665 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288 x y
       grind)
    | exact superpose eq288 eq16
    | (have j1 := eq288 x y
       grind)
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq2306 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq321
    | exact resolve eq321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq2403 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2306 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2306
    | (have j0 := eq2306 X0 X1
       grind)
    | exact resolve eq2306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq3661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq665
       have i₂ := eq2403 y x
       grind)
    | exact superpose eq2403 eq665
    | (have j1 := eq2403 (σ y) (σ x)
       grind)
    | (have r₁ := eq665
       have r₂ := eq2403 y x
       grind)
    | exact resolve eq665 eq2403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq3662 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3661
  have eq3880 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3662
       grind)
    | exact superpose eq3662 eq16
    | exact resolve eq16 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3882 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3662
       grind)
    | exact superpose eq3662 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3662
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3662
       grind)
    | exact resolve eq13 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3885 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3882
  have eq3888 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3885
       have i₂ := eq38 x
       grind)
    | exact superpose eq38 eq3885
    | exact resolve eq3885 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3885
  have eq3893 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3888
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3888
    | exact resolve eq3888 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3888
  have eq13291 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2403 y x
       have i₂ := eq3893
       grind)
    | exact superpose eq3893 eq2403
    | (have j0 := eq2403 y x
       grind)
    | exact resolve eq2403 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq13367 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq13291
  have eq13399 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13367
       have r₂ := eq3880
       grind)
    | exact resolve eq13367 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13367
  have eq13767 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq13399
       grind)
    | exact superpose eq13399 eq10
    | exact resolve eq10 eq13399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13399
  have eq13856 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13767
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13767
    | exact resolve eq13767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13767
  have eq14066 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq13856
       grind)
    | exact superpose eq13856 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13856
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq13856
       grind)
    | exact resolve eq13 eq13856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14068 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq14066
  have eq14069 : x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq14068
  have eq14373 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq682 x y
       have i₂ := eq14069
       grind)
    | exact superpose eq14069 eq682
    | (have j0 := eq682 x y
       grind)
    | exact resolve eq682 eq14069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14069
  have eq14395 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq14373
  have eq15127 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14395
       grind)
    | exact superpose eq14395 eq16
    | exact resolve eq16 eq14395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14395
  have eq15653 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15127
       have i₂ := eq13856
       grind)
    | exact superpose eq13856 eq15127
    | exact resolve eq15127 eq13856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13856 eq15127
  have eq15654 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq15653
  have eq15655 : x = (M.op x x) := by grind
  clear eq15654
  have eq15942 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq15655
       grind)
    | exact superpose eq15655 eq12
    | exact resolve eq12 eq15655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15945 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq96 x x
       have i₂ := eq15655
       grind)
    | exact superpose eq15655 eq96
    | exact resolve eq96 eq15655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq15655
  have eq16413 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15945 (σ y)
       have i₂ := eq3662
       grind)
    | exact superpose eq3662 eq15945
    | (have j0 := eq15945 (σ y)
       grind)
    | (have r₁ := eq15945 (σ y)
       have r₂ := eq3662
       grind)
    | exact resolve eq15945 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662 eq15945
  have eq16422 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16413
  have eq16431 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16422
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16422
    | exact resolve eq16422 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16422
  have eq16506 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2403 y x
       have i₂ := eq16431
       grind)
    | exact superpose eq16431 eq2403
    | (have j0 := eq2403 y x
       grind)
    | exact resolve eq2403 eq16431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq16509 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq16431
       grind)
    | exact superpose eq16431 eq10
    | exact resolve eq10 eq16431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16431
  have eq16591 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq16506
  have eq16626 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16509
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16509
    | exact resolve eq16509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16509
  have eq16627 : x = (M.op x y) := by
    first
    | (have r₁ := eq16591
       have r₂ := eq3880
       grind)
    | exact resolve eq16591 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880 eq16591
  have eq16637 : x = (k x y) := by
    first
    | (have j1 := eq15942 y
       grind)
    | (have r₁ := eq16626
       have r₂ := eq15942 y
       grind)
    | exact resolve eq16626 eq15942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15942 eq16626
  have eq17157 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq682 x y
       have i₂ := eq16637
       grind)
    | exact superpose eq16637 eq682
    | (have j0 := eq682 x y
       grind)
    | exact resolve eq682 eq16637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq16637
  have eq17181 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17157
  have eq17988 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17181
       grind)
    | exact superpose eq17181 eq16
    | exact resolve eq16 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17181
  have eq18006 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq17988
       have i₂ := eq16627
       grind)
    | exact superpose eq16627 eq17988
    | exact resolve eq17988 eq16627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16627 eq17988
  have eq18007 : False := by grind
  exact eq18007

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxx_y_pxy_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq12
    | exact resolve eq12 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq129 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq126 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq126 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq126 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq126 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq126 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq246 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq129 (σ X0) (σ X1)
       grind)
    | exact superpose eq129 eq15
    | (have j1 := eq129 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq129 (τ X0) X1
       grind)
    | exact superpose eq129 eq17
    | (have j1 := eq129 (τ X0) X1
       grind)
    | exact resolve eq17 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq129
  have eq1711 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq248 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq248
    | exact resolve eq248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq1787 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1711 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1711
    | (have j0 := eq1711 X0 X1
       grind)
    | exact resolve eq1711 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq2815 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq246 x y
       grind)
    | exact superpose eq246 eq16
    | (have j1 := eq246 x y
       grind)
    | exact resolve eq16 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2847 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq7341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2815
       have i₂ := eq1787 x y
       grind)
    | exact superpose eq1787 eq2815
    | (have j1 := eq1787 (σ x) (σ y)
       grind)
    | (have r₁ := eq2815
       have r₂ := eq1787 x y
       grind)
    | exact resolve eq2815 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq7342 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq7341
  have eq7632 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7342
       grind)
    | exact superpose eq7342 eq16
    | exact resolve eq16 eq7342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7635 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq7342
       grind)
    | exact superpose eq7342 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7342
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq7342
       grind)
    | exact resolve eq13 eq7342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7638 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq7635
  have eq7639 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7638
       have i₂ := eq38 x
       grind)
    | exact superpose eq38 eq7638
    | exact resolve eq7638 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7638
  have eq7644 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7639
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7639
    | exact resolve eq7639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7639
  have eq19740 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1787 x y
       have i₂ := eq7644
       grind)
    | exact superpose eq7644 eq1787
    | (have j0 := eq1787 x y
       grind)
    | exact resolve eq1787 eq7644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7644
  have eq19824 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq19740
  have eq19860 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19824
       have r₂ := eq7632
       grind)
    | exact resolve eq19824 eq7632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19824
  have eq20219 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq19860
       grind)
    | exact superpose eq19860 eq10
    | exact resolve eq10 eq19860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19860
  have eq20310 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20219
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq20219
    | exact resolve eq20219 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20219
  have eq20695 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20310
       grind)
    | exact superpose eq20310 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20310
       grind)
    | exact resolve eq13 eq20310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20697 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by grind
  clear eq20695
  have eq20698 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq20697
  have eq21412 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2847 x y
       have i₂ := eq20698
       grind)
    | exact superpose eq20698 eq2847
    | (have j0 := eq2847 x y
       grind)
    | exact resolve eq2847 eq20698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20698
  have eq21423 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq21412
  have eq22640 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21423
       grind)
    | exact superpose eq21423 eq16
    | exact resolve eq16 eq21423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21423
  have eq23156 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22640
       have i₂ := eq20310
       grind)
    | exact superpose eq20310 eq22640
    | exact resolve eq22640 eq20310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20310 eq22640
  have eq23157 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq23156
  have eq23158 : y = (M.op x x) := by grind
  clear eq23157
  have eq23506 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq23158
       grind)
    | exact superpose eq23158 eq12
    | exact resolve eq12 eq23158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23511 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (σ y) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq98 x x
       have i₂ := eq23158
       grind)
    | exact superpose eq23158 eq98
    | exact resolve eq98 eq23158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq23158
  have eq28225 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23511 (σ y)
       have i₂ := eq7342
       grind)
    | exact superpose eq7342 eq23511
    | (have j0 := eq23511 (σ y)
       grind)
    | (have r₁ := eq23511 (σ y)
       have r₂ := eq7342
       grind)
    | exact resolve eq23511 eq7342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7342 eq23511
  have eq28230 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq28225
  have eq28237 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28230
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq28230
    | exact resolve eq28230 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28230
  have eq28747 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1787 x y
       have i₂ := eq28237
       grind)
    | exact superpose eq28237 eq1787
    | (have j0 := eq1787 x y
       grind)
    | exact resolve eq1787 eq28237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq28752 : (k x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq28237
       grind)
    | exact superpose eq28237 eq10
    | exact resolve eq10 eq28237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28237
  have eq28842 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq28747
  have eq28876 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28752
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq28752
    | exact resolve eq28752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28752
  have eq28877 : y = (M.op x y) := by
    first
    | (have r₁ := eq28842
       have r₂ := eq7632
       grind)
    | exact resolve eq28842 eq7632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7632 eq28842
  have eq28886 : y = (k x y) := by
    first
    | (have j1 := eq23506 y
       grind)
    | (have r₁ := eq28876
       have r₂ := eq23506 y
       grind)
    | exact resolve eq28876 eq23506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23506 eq28876
  have eq30022 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2847 x y
       have i₂ := eq28886
       grind)
    | exact superpose eq28886 eq2847
    | (have j0 := eq2847 x y
       grind)
    | exact resolve eq2847 eq28886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847 eq28886
  have eq30033 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq30022
  have eq32182 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30033
       grind)
    | exact superpose eq30033 eq16
    | exact resolve eq16 eq30033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30033
  have eq32196 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq32182
       have i₂ := eq28877
       grind)
    | exact superpose eq28877 eq32182
    | exact resolve eq32182 eq28877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28877 eq32182
  have eq32197 : False := by grind
  exact eq32197

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_pxx_pxy_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | (have j0 := eq52 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq88 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq73
    | (have j0 := eq73 X0 X1
       grind)
    | exact resolve eq73 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq211 X0 X1
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq211 X0 X1
       have r₂ := eq96 (k X0 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq211 X0 X1
       have r₂ := eq96 (M.op X0 X0) (k X0 X1)
       grind)
    | exact resolve eq211 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq211
  have eq248 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq91 (τ X0) X1
       grind)
    | exact superpose eq91 eq18
    | (have j1 := eq91 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq91
  have eq636 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq248 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq248
    | exact resolve eq248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq673 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq636
    | (have j0 := eq636 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq690 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq220 x y
       grind)
    | exact superpose eq220 eq16
    | (have j1 := eq220 x y
       grind)
    | exact resolve eq16 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq1091 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq690
       have i₂ := eq673 x y
       grind)
    | exact superpose eq673 eq690
    | (have j1 := eq673 (σ x) (σ y)
       grind)
    | (have r₁ := eq690
       have r₂ := eq673 x y
       grind)
    | (have r₁ := eq690
       have r₂ := eq673 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq690
       have r₂ := eq673 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq690 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq690
  have eq1092 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1091
  have eq1175 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1092
       grind)
    | exact superpose eq1092 eq10
    | exact resolve eq10 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1211 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1175
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1175
    | exact resolve eq1175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1212 : x = y := by grind
  clear eq1211
  have eq1326 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq16
    | exact resolve eq16 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1327 : False := by grind
  exact eq1327

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | (have j0 := eq52 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq88 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq73
    | (have j0 := eq73 X0 X1
       grind)
    | exact resolve eq73 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq211 X0 X1
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq211 X0 X1
       have r₂ := eq96 (k X0 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq211 X0 X1
       have r₂ := eq96 (M.op X0 X0) (k X0 X1)
       grind)
    | exact resolve eq211 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq211
  have eq248 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq91 (τ X0) X1
       grind)
    | exact superpose eq91 eq18
    | (have j1 := eq91 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq91
  have eq636 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq248 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq248
    | exact resolve eq248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq673 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq636
    | (have j0 := eq636 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq690 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq220 x y
       grind)
    | exact superpose eq220 eq16
    | (have j1 := eq220 x y
       grind)
    | exact resolve eq16 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq1091 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq690
       have i₂ := eq673 x y
       grind)
    | exact superpose eq673 eq690
    | (have j1 := eq673 (σ x) (σ y)
       grind)
    | (have r₁ := eq690
       have r₂ := eq673 x y
       grind)
    | (have r₁ := eq690
       have r₂ := eq673 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq690
       have r₂ := eq673 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq690 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq690
  have eq1092 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1091
  have eq1175 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1092
       grind)
    | exact superpose eq1092 eq10
    | exact resolve eq10 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1211 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1175
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1175
    | exact resolve eq1175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1212 : x = y := by grind
  clear eq1211
  have eq1326 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq16
    | exact resolve eq16 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1327 : False := by grind
  exact eq1327

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq53 (σ X1) (σ X0)
       grind)
    | exact superpose eq53 eq15
    | (have j1 := eq53 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq53 (τ X1) X0
       grind)
    | exact superpose eq53 eq18
    | (have j1 := eq53 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq53
  have eq184 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq208 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq184
    | (have j0 := eq184 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq566 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq566
       have i₂ := eq208 y x
       grind)
    | exact superpose eq208 eq566
    | (have j1 := eq208 (σ x) (σ y)
       grind)
    | (have r₁ := eq566
       have r₂ := eq208 y x
       grind)
    | (have r₁ := eq566
       have r₂ := eq208 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq566
       have r₂ := eq208 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq566 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq566
  have eq663 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq662
  have eq758 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq663
       grind)
    | exact superpose eq663 eq10
    | exact resolve eq10 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq793 : x = y ∨ x = y := by
    first
    | (have i₁ := eq758
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq758
    | exact resolve eq758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq794 : x = y := by grind
  clear eq793
  have eq965 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq16
    | exact resolve eq16 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq966 : False := by grind
  exact eq966

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq89 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq89 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq172 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq92 (σ X1) (σ X0)
       grind)
    | exact superpose eq92 eq15
    | (have j1 := eq92 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq92 (τ X1) X0
       grind)
    | exact superpose eq92 eq18
    | (have j1 := eq92 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq92
  have eq584 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq174
    | exact resolve eq174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq622 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq584
    | (have j0 := eq584 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq584 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq1750 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq172 x y
       grind)
    | exact superpose eq172 eq16
    | (have j1 := eq172 x y
       grind)
    | exact resolve eq16 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq1955 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1750
       have i₂ := eq622 y x
       grind)
    | exact superpose eq622 eq1750
    | (have j1 := eq622 (σ x) (σ y)
       grind)
    | (have r₁ := eq1750
       have r₂ := eq622 y x
       grind)
    | (have r₁ := eq1750
       have r₂ := eq622 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1750
       have r₂ := eq622 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1750 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq1750
  have eq1956 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1955
  have eq1973 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq10
    | exact resolve eq10 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq2019 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1973
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1973
    | exact resolve eq1973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq2020 : x = y := by grind
  clear eq2019
  have eq2085 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2020
       grind)
    | exact superpose eq2020 eq16
    | exact resolve eq16 eq2020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2086 : False := by grind
  exact eq2086

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq54 (σ X0) (σ X1)
       grind)
    | exact superpose eq54 eq15
    | (have j1 := eq54 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq54 (τ X0) X1
       grind)
    | exact superpose eq54 eq18
    | (have j1 := eq54 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq54
  have eq168 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60
    | exact resolve eq60 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq168
    | (have j0 := eq168 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq571 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq591 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq571
       have i₂ := eq190 x y
       grind)
    | exact superpose eq190 eq571
    | (have j1 := eq190 (σ x) (σ y)
       grind)
    | (have r₁ := eq571
       have r₂ := eq190 x y
       grind)
    | (have r₁ := eq571
       have r₂ := eq190 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq571
       have r₂ := eq190 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq571 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq571
  have eq592 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq591
  have eq673 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq592
       grind)
    | exact superpose eq592 eq10
    | exact resolve eq10 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq708 : x = y ∨ x = y := by
    first
    | (have i₁ := eq673
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq673
    | exact resolve eq673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq709 : x = y := by grind
  clear eq708
  have eq798 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq709
       grind)
    | exact superpose eq709 eq16
    | exact resolve eq16 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq799 : False := by grind
  exact eq799

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq46 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X2
       have i₂ := eq14 X1 X2
       grind)
    | (have i₁ := eq14 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X1 X2
       have j1 := eq14 X1 X2
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X1 X1 X2
       have j1 := eq54 X1 X1 X2
       grind)
    | (have r₁ := eq46 X0 X1 X2
       have r₂ := eq54 X0 X1 X2
       grind)
    | (have r₁ := eq46 X1 X0 X2
       have r₂ := eq54 X0 X1 X2
       grind)
    | (have r₁ := eq46 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq54 X0 X1 X2
       grind)
    | exact resolve eq46 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq54
  have eq126 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq128 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq183 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq128 (σ X0) (σ X1)
       grind)
    | exact superpose eq128 eq15
    | (have j1 := eq128 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq128 (τ X0) X1
       grind)
    | exact superpose eq128 eq18
    | (have j1 := eq128 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq128
  have eq316 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq185 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq185
    | exact resolve eq185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq335 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq316
    | (have j0 := eq316 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq1461 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq183 x y
       grind)
    | exact superpose eq183 eq16
    | (have j1 := eq183 x y
       grind)
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1548 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1461
       have i₂ := eq335 x y
       grind)
    | exact superpose eq335 eq1461
    | (have j1 := eq335 (σ x) (σ y)
       grind)
    | (have r₁ := eq1461
       have r₂ := eq335 x y
       grind)
    | (have r₁ := eq1461
       have r₂ := eq335 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1461
       have r₂ := eq335 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1461 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq1461
  have eq1549 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1548
  have eq1632 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1549
       grind)
    | exact superpose eq1549 eq10
    | exact resolve eq10 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1673 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1632
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1632
    | exact resolve eq1632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1674 : x = y := by grind
  clear eq1673
  have eq1748 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq16
    | exact resolve eq16 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1749 : False := by grind
  exact eq1749

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq113 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq148 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq270 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq10
    | (have j1 := eq59 X0 X1
       grind)
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq1159 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1303 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq285 x y
       grind)
    | exact superpose eq285 eq16
    | (have j1 := eq285 x y
       grind)
    | exact resolve eq16 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1492 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1656 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1492 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1492
    | (have j0 := eq1492 X0 X1
       grind)
    | exact resolve eq1492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq2057 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq113
    | (have j0 := eq113 X1 (σ X0)
       grind)
    | (have r₁ := eq113 X0 (σ X0)
       have r₂ := eq39 X0
       grind)
    | exact resolve eq113 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2086 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2057 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2057
    | (have j0 := eq2057 X0 X1
       grind)
    | exact resolve eq2057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq27457 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1303
       have i₂ := eq1656 y x
       grind)
    | exact superpose eq1656 eq1303
    | (have j1 := eq1656 x y
       grind)
    | (have r₁ := eq1303
       have r₂ := eq1656 y x
       grind)
    | (have r₁ := eq1303
       have r₂ := eq1656 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1303
       have r₂ := eq1656 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1303 eq1656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303 eq1656
  have eq27458 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27457
  have eq27459 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27458
  have eq28451 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq27459
       grind)
    | exact superpose eq27459 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq27459
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq27459
       grind)
    | exact resolve eq12 eq27459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28557 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2086 y X0
       have i₂ := eq27459
       grind)
    | exact superpose eq27459 eq2086
    | (have j0 := eq2086 X0 x
       grind)
    | exact resolve eq2086 eq27459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086 eq27459
  have eq60428 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq28451 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28451
  have eq60522 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125 x y
       have i₂ := eq60428
       grind)
    | exact superpose eq60428 eq125
    | (have j0 := eq125 x y
       grind)
    | exact resolve eq125 eq60428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq60428
  have eq60531 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq60522
  have eq60537 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1159 x y
       grind)
    | (have r₁ := eq60531
       have r₂ := eq1159 x y
       grind)
    | (have r₁ := eq60531
       have r₂ := eq1159 y x
       grind)
    | exact resolve eq60531 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159 eq60531
  have eq124034 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq28557 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28557
  have eq124048 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq124034
       grind)
    | exact superpose eq124034 eq16
    | exact resolve eq16 eq124034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124034
  have eq124114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq124048
       have i₂ := eq60537
       grind)
    | exact superpose eq60537 eq124048
    | exact resolve eq124048 eq60537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60537 eq124048
  have eq124133 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq124114
  have eq124134 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq124133
  have eq124136 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq124134
       grind)
    | exact superpose eq124134 eq10
    | exact resolve eq10 eq124134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124134
  have eq124546 : x = y ∨ x = y := by
    first
    | (have i₁ := eq124136
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq124136
    | exact resolve eq124136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124136
  have eq124547 : x = y := by grind
  clear eq124546
  have eq124549 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124547
       grind)
    | exact superpose eq124547 eq16
    | exact resolve eq16 eq124547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124547
  have eq124550 : False := by grind
  exact eq124550

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  clear eq17
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq84 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq16
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq358 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq90
    | (have j0 := eq90 (τ X0) (τ X1)
       grind)
    | exact resolve eq90 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq358 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq358
    | (have j0 := eq358 X0 X1
       grind)
    | exact resolve eq358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq368 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq365
    | (have j0 := eq365 X0 X1
       grind)
    | exact resolve eq365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq370 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq371 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq372 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq373 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq423 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq91
    | (have j0 := eq91 (τ X0) (τ X1)
       grind)
    | exact resolve eq91 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq431 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq423
    | (have j0 := eq423 X0 X1
       grind)
    | exact resolve eq423 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq434 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq431 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | (have j0 := eq431 X0 X1
       grind)
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq436 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq434
    | (have j0 := eq434 X0 X1
       grind)
    | exact resolve eq434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq437 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq436
    | (have j0 := eq436 X0 X1
       grind)
    | exact resolve eq436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq438 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq437
    | (have j0 := eq437 X0 X1
       grind)
    | exact resolve eq437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq439 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq438
    | (have j0 := eq438 X0 X1
       grind)
    | exact resolve eq438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq485 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq84
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq486 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq485
  have eq3351 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq486
       grind)
    | exact superpose eq486 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq486
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq486
       grind)
    | exact resolve eq13 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3353 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq486
  have eq3354 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3351
  have eq3355 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3354
       have r₂ := eq3353
       grind)
    | exact resolve eq3354 eq3353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353 eq3354
  have eq3357 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3355
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3355
    | exact resolve eq3355 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq20899 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3357
       grind)
    | exact superpose eq3357 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3357
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3357
       grind)
    | exact resolve eq12 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq20900 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20899
  have eq20903 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20900
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20900
    | exact resolve eq20900 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20900
  have eq21378 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq20903
       grind)
    | exact superpose eq20903 eq10
    | exact resolve eq10 eq20903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20903
  have eq21530 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21378
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq21378
    | exact resolve eq21378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21378
  have eq21533 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq373 x y
       grind)
    | (have r₁ := eq21530
       have r₂ := eq373 x y
       grind)
    | exact resolve eq21530 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq21530
  have eq21784 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq21533
       grind)
    | exact superpose eq21533 eq10
    | exact resolve eq10 eq21533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21533
  have eq21936 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21784
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21784
    | exact resolve eq21784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21784
  have eq21937 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq439 x y
       grind)
    | (have r₁ := eq21936
       have r₂ := eq439 x y
       grind)
    | exact resolve eq21936 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq21936
  have eq22182 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq21937
       grind)
    | exact superpose eq21937 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21937
       grind)
    | exact resolve eq13 eq21937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22184 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq22185 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq22182
  have eq22186 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22185
       have r₂ := eq22184
       grind)
    | exact resolve eq22185 eq22184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22185
  have eq22953 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91 x y
       have i₂ := eq22186
       grind)
    | exact superpose eq22186 eq91
    | (have j0 := eq91 x y
       grind)
    | exact resolve eq91 eq22186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq22997 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22953
  have eq135577 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22997
       grind)
    | exact superpose eq22997 eq16
    | exact resolve eq16 eq22997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22997
  have eq135684 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135577
       have i₂ := eq21937
       grind)
    | exact superpose eq21937 eq135577
    | exact resolve eq135577 eq21937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135577
  have eq135687 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq135684
  have eq135688 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq135687
       have r₂ := eq22184
       grind)
    | exact resolve eq135687 eq22184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135687
  have eq135744 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq135688
       grind)
    | exact superpose eq135688 eq16
    | exact resolve eq16 eq135688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135745 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq135688
       grind)
    | exact superpose eq135688 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq135688
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq135688
       grind)
    | exact resolve eq12 eq135688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135688
  have eq135746 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq135745
  have eq135749 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135746
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq135746
    | exact resolve eq135746 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135746
  have eq135799 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135744
       have i₂ := eq21937
       grind)
    | exact superpose eq21937 eq135744
    | exact resolve eq135744 eq21937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21937 eq135744
  have eq135803 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq135799
       have r₂ := eq22184
       grind)
    | exact resolve eq135799 eq22184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22184 eq135799
  have eq135879 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135749
       have i₂ := eq22186
       grind)
    | exact superpose eq22186 eq135749
    | exact resolve eq135749 eq22186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22186
  have eq135917 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq135749
       grind)
    | exact superpose eq135749 eq10
    | exact resolve eq10 eq135749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135749
  have eq136012 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq135879
  have eq136069 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135917
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq135917
    | exact resolve eq135917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135917
  have eq136096 : x = (M.op x y) := by
    first
    | (have r₁ := eq136012
       have r₂ := eq135803
       grind)
    | exact resolve eq136012 eq135803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135803 eq136012
  have eq136097 : y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq136069
       have r₂ := eq12 x y
       grind)
    | exact resolve eq136069 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136069
  have eq136171 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq136097
       grind)
    | exact superpose eq136097 eq90
    | (have j0 := eq90 x y
       grind)
    | exact resolve eq90 eq136097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq136210 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq136171
  have eq137739 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq136210
       grind)
    | exact superpose eq136210 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq136210
       grind)
    | exact resolve eq13 eq136210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137741 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq136210
  have eq137742 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq137739
  have eq137743 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq137742
       have r₂ := eq137741
       grind)
    | exact resolve eq137742 eq137741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137742
  have eq137746 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq137743
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq137743
    | exact resolve eq137743 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137743
  have eq137748 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq137746
       have i₂ := eq136097
       grind)
    | exact superpose eq136097 eq137746
    | exact resolve eq137746 eq136097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136097 eq137746
  have eq137749 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq137748
       have r₂ := eq137741
       grind)
    | exact resolve eq137748 eq137741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137741 eq137748
  have eq137806 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq137749
       grind)
    | exact superpose eq137749 eq16
    | exact resolve eq16 eq137749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137749
  have eq137810 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq137806
       have i₂ := eq136096
       grind)
    | exact superpose eq136096 eq137806
    | exact resolve eq137806 eq136096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136096 eq137806
  have eq137811 : False := by grind
  exact eq137811

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation2847 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2847 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
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
  have eq44 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq57 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45 x y
       grind)
    | exact superpose eq45 eq16
    | (have j1 := eq45 x y
       grind)
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq303 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44
    | exact resolve eq44 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq335 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq697 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq57
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq57
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq57
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq57
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq698 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq697
  have eq3751 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq16
    | exact resolve eq16 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3752 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq698
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq698
       grind)
    | exact resolve eq13 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq3753 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3752
  have eq3754 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3753
  have eq3756 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3754
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3754
    | exact resolve eq3754 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754
  have eq6422 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq335 y x
       have i₂ := eq3756
       grind)
    | exact superpose eq3756 eq335
    | (have j0 := eq335 y x
       grind)
    | exact resolve eq335 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq6424 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq3756
       grind)
    | exact superpose eq3756 eq10
    | exact resolve eq10 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq6463 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6422
  have eq6491 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6424
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6424
    | exact resolve eq6424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6424
  have eq6492 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6463
       have r₂ := eq3751
       grind)
    | exact resolve eq6463 eq3751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3751 eq6463
  have eq6495 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq6491
       have r₂ := eq13 x y
       grind)
    | exact resolve eq6491 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6841 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59 x y
       have i₂ := eq6495
       grind)
    | exact superpose eq6495 eq59
    | (have j0 := eq59 x y
       grind)
    | exact resolve eq59 eq6495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq6495
  have eq6844 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6841
  have eq6845 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6844
  have eq7047 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq6845
       grind)
    | exact superpose eq6845 eq16
    | exact resolve eq16 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq7257 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7047
       have i₂ := eq6492
       grind)
    | exact superpose eq6492 eq7047
    | exact resolve eq7047 eq6492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6492 eq7047
  have eq7258 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7257
  have eq7259 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq7258
  have eq7419 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7259
       grind)
    | exact superpose eq7259 eq10
    | exact resolve eq10 eq7259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7259
  have eq7492 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7419
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7419
    | exact resolve eq7419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7419
  have eq7493 : x = y := by grind
  clear eq7492
  have eq7658 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7493
       grind)
    | exact superpose eq7493 eq16
    | exact resolve eq16 eq7493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7493
  have eq7659 : False := by grind
  exact eq7659

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation2847 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2847 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq78 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq374 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq405 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | exact resolve eq374 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq800 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq78
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq78 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq801 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq800
  have eq4278 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq801
       grind)
    | exact superpose eq801 eq16
    | exact resolve eq16 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4279 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq801
       grind)
    | exact superpose eq801 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq801
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq801
       grind)
    | exact resolve eq13 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq4280 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4279
  have eq4281 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4280
  have eq4283 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4281
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4281
    | exact resolve eq4281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq6994 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq405 x y
       have i₂ := eq4283
       grind)
    | exact superpose eq4283 eq405
    | (have j0 := eq405 x y
       grind)
    | exact resolve eq405 eq4283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq6996 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq4283
       grind)
    | exact superpose eq4283 eq10
    | exact resolve eq10 eq4283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq7034 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6994
  have eq7060 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6996
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6996
    | exact resolve eq6996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996
  have eq7061 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7034
       have r₂ := eq4278
       grind)
    | exact resolve eq7034 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278 eq7034
  have eq7064 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq7060
       have r₂ := eq13 y x
       grind)
    | exact resolve eq7060 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7060
  have eq7477 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq80 x y
       have i₂ := eq7064
       grind)
    | exact superpose eq7064 eq80
    | (have j0 := eq80 x y
       grind)
    | exact resolve eq80 eq7064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq7064
  have eq7480 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7477
  have eq7481 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7480
  have eq7709 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq7481
       grind)
    | exact superpose eq7481 eq16
    | exact resolve eq16 eq7481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7481
  have eq7892 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7709
       have i₂ := eq7061
       grind)
    | exact superpose eq7061 eq7709
    | exact resolve eq7709 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7061 eq7709
  have eq7893 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7892
  have eq7894 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq7893
  have eq8062 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7894
       grind)
    | exact superpose eq7894 eq10
    | exact resolve eq10 eq7894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7894
  have eq8130 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8062
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8062
    | exact resolve eq8062 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8062
  have eq8131 : x = y := by grind
  clear eq8130
  have eq8277 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8131
       grind)
    | exact superpose eq8131 eq16
    | exact resolve eq16 eq8131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8131
  have eq8278 : False := by grind
  exact eq8278

/-- `Equation2862`: `x = ((x ◇ (y ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation2862 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2862 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2862.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26 (σ X0)
       grind)
    | exact superpose eq26 eq15
    | exact resolve eq15 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq28
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq45 (σ X1) (σ X0)
       grind)
    | exact superpose eq45 eq15
    | (have j1 := eq45 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq45 (τ X1) X0
       grind)
    | exact superpose eq45 eq18
    | (have j1 := eq45 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45
  have eq208 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq208
    | (have j0 := eq208 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq601 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq751 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq601
       have i₂ := eq235 y x
       grind)
    | exact superpose eq235 eq601
    | (have j1 := eq235 (σ x) (σ y)
       grind)
    | (have r₁ := eq601
       have r₂ := eq235 y x
       grind)
    | (have r₁ := eq601
       have r₂ := eq235 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq601
       have r₂ := eq235 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq601 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq601
  have eq752 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq751
  have eq859 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq10
    | exact resolve eq10 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq895 : x = y ∨ x = y := by
    first
    | (have i₁ := eq859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq859
    | exact resolve eq859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq896 : x = y := by grind
  clear eq895
  have eq946 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq16
    | exact resolve eq16 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq947 : False := by grind
  exact eq947

/-- `Equation2862`: `x = ((x ◇ (y ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation2862 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2862 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2862.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq30
    | exact resolve eq30 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq33 X1
       grind)
    | exact superpose eq33 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq47
    | (have j0 := eq47 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq47 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq80 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq80 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq80 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq192 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq199 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq88 X1 X0
       grind)
    | (have r₁ := eq192 X1 X0
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq88 (k X1 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq88 (M.op X1 X1) (k X1 X0)
       grind)
    | exact resolve eq192 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq192
  have eq330 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq83 (τ X1) X0
       grind)
    | exact superpose eq83 eq18
    | (have j1 := eq83 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq83
  have eq654 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
  have eq795 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq330
    | exact resolve eq330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq842 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq795
    | (have j0 := eq795 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq1250 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq654
       have i₂ := eq842 y x
       grind)
    | exact superpose eq842 eq654
    | (have j1 := eq842 (σ x) (σ y)
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 y x
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq654
       have r₂ := eq842 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq654 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq842
  have eq1251 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1250
  have eq1336 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1251
       grind)
    | exact superpose eq1251 eq10
    | exact resolve eq10 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1373 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1336
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1336
    | exact resolve eq1336 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1374 : x = y := by grind
  clear eq1373
  have eq1507 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq16
    | exact resolve eq16 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1508 : False := by grind
  exact eq1508

/-- `Equation2862`: `x = ((x ◇ (y ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_Equation2862 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2862 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2862.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26 (σ X0)
       grind)
    | exact superpose eq26 eq15
    | exact resolve eq15 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq28
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28
  have eq39 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq103 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq136 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq251 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq51 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq10
    | (have j1 := eq51 X0 X1
       grind)
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq262 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq251
    | (have j0 := eq251 X0 X1
       grind)
    | exact resolve eq251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq1153 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1505 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq16
    | (have j1 := eq262 x y
       grind)
    | exact resolve eq16 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq1659 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40
    | exact resolve eq40 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1851 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1659 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1659
    | (have j0 := eq1659 X0 X1
       grind)
    | exact resolve eq1659 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq2222 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X1 (σ X0)
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq103
    | (have j0 := eq103 X1 (σ X0)
       grind)
    | (have r₁ := eq103 X0 (σ X0)
       have r₂ := eq31 X0
       grind)
    | exact resolve eq103 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq2251 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2222 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2222
    | (have j0 := eq2222 X0 X1
       grind)
    | exact resolve eq2222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq30807 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1505
       have i₂ := eq1851 y x
       grind)
    | exact superpose eq1851 eq1505
    | (have j1 := eq1851 x y
       grind)
    | (have r₁ := eq1505
       have r₂ := eq1851 y x
       grind)
    | (have r₁ := eq1505
       have r₂ := eq1851 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1505
       have r₂ := eq1851 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1505 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505 eq1851
  have eq30808 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30807
  have eq30809 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30808
  have eq30898 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq30809
       grind)
    | exact superpose eq30809 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq30809
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq30809
       grind)
    | exact resolve eq12 eq30809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31009 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2251 y X0
       have i₂ := eq30809
       grind)
    | exact superpose eq30809 eq2251
    | (have j0 := eq2251 X0 x
       grind)
    | exact resolve eq2251 eq30809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251 eq30809
  have eq71430 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq30898 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30898
  have eq71614 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq116 x y
       have i₂ := eq71430
       grind)
    | exact superpose eq71430 eq116
    | (have j0 := eq116 x y
       grind)
    | exact resolve eq116 eq71430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq71430
  have eq71651 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq71614
  have eq71681 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1153 x y
       grind)
    | (have r₁ := eq71651
       have r₂ := eq1153 y x
       grind)
    | (have r₁ := eq71651
       have r₂ := eq1153 x y
       grind)
    | exact resolve eq71651 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153 eq71651
  have eq134690 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq31009 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31009
  have eq134704 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq134690
       grind)
    | exact superpose eq134690 eq16
    | exact resolve eq16 eq134690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134690
  have eq134752 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq134704
       have i₂ := eq71681
       grind)
    | exact superpose eq71681 eq134704
    | exact resolve eq134704 eq71681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71681 eq134704
  have eq134771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq134752
  have eq134772 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq134771
  have eq134774 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq134772
       grind)
    | exact superpose eq134772 eq10
    | exact resolve eq10 eq134772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134772
  have eq135238 : x = y ∨ x = y := by
    first
    | (have i₁ := eq134774
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq134774
    | exact resolve eq134774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134774
  have eq135239 : x = y := by grind
  clear eq135238
  have eq135241 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq135239
       grind)
    | exact superpose eq135239 eq16
    | exact resolve eq16 eq135239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135239
  have eq135242 : False := by grind
  exact eq135242

/-- `Equation2862`: `x = ((x ◇ (y ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2862 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2862 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2862.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq81 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq16
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq466 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq88
    | (have j0 := eq88 (τ X0) (τ X1)
       grind)
    | exact resolve eq88 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq466
    | (have j0 := eq466 X0 X1
       grind)
    | exact resolve eq466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq476 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq473 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq473
    | (have j0 := eq473 X0 X1
       grind)
    | exact resolve eq473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq478 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq476
    | (have j0 := eq476 X0 X1
       grind)
    | exact resolve eq476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq479 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq478
    | (have j0 := eq478 X0 X1
       grind)
    | exact resolve eq478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq480 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq479 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq479
    | (have j0 := eq479 X0 X1
       grind)
    | exact resolve eq479 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq481 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq480 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq480
    | (have j0 := eq480 X0 X1
       grind)
    | exact resolve eq480 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq498 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq89
    | (have j0 := eq89 (τ X0) (τ X1)
       grind)
    | exact resolve eq89 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq507 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq498
    | (have j0 := eq498 X0 X1
       grind)
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq510 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq507
    | (have j0 := eq507 X0 X1
       grind)
    | exact resolve eq507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq512 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq510
    | (have j0 := eq510 X0 X1
       grind)
    | exact resolve eq510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq513 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq512
    | (have j0 := eq512 X0 X1
       grind)
    | exact resolve eq512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq514 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq513
    | (have j0 := eq513 X0 X1
       grind)
    | exact resolve eq513 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq515 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq514
    | (have j0 := eq514 X0 X1
       grind)
    | exact resolve eq514 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq528 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq81
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq529 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq528
  have eq4040 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq529
       grind)
    | exact superpose eq529 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq529
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq529
       grind)
    | exact resolve eq13 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4043 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq529
  have eq4044 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4040
  have eq4045 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4044
       have r₂ := eq4043
       grind)
    | exact resolve eq4044 eq4043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4043 eq4044
  have eq4047 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4045
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4045
    | exact resolve eq4045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4045
  have eq23751 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq4047
       grind)
    | exact superpose eq4047 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4047
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4047
       grind)
    | exact resolve eq12 eq4047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq23757 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23751
  have eq23760 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23757
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq23757
    | exact resolve eq23757 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23757
  have eq24526 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq23760
       grind)
    | exact superpose eq23760 eq10
    | exact resolve eq10 eq23760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23760
  have eq24682 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24526
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq24526
    | exact resolve eq24526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24526
  have eq24685 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq481 x y
       grind)
    | (have r₁ := eq24682
       have r₂ := eq481 x y
       grind)
    | exact resolve eq24682 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq24682
  have eq24960 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq24685
       grind)
    | exact superpose eq24685 eq10
    | exact resolve eq10 eq24685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24685
  have eq25118 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24960
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24960
    | exact resolve eq24960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24960
  have eq25119 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq515 x y
       grind)
    | (have r₁ := eq25118
       have r₂ := eq515 x y
       grind)
    | exact resolve eq25118 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq25118
  have eq25398 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25119
       grind)
    | exact superpose eq25119 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25119
       grind)
    | exact resolve eq13 eq25119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25404 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq25405 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq25398
  have eq25406 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25405
       have r₂ := eq25404
       grind)
    | exact resolve eq25405 eq25404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25405
  have eq26186 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89 x y
       have i₂ := eq25406
       grind)
    | exact superpose eq25406 eq89
    | (have j0 := eq89 x y
       grind)
    | exact resolve eq89 eq25406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq26232 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26186
  have eq158172 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26232
       grind)
    | exact superpose eq26232 eq16
    | exact resolve eq16 eq26232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26232
  have eq158217 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158172
       have i₂ := eq25119
       grind)
    | exact superpose eq25119 eq158172
    | exact resolve eq158172 eq25119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158172
  have eq158220 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq158217
  have eq158221 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq158220
       have r₂ := eq25404
       grind)
    | exact resolve eq158220 eq25404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158220
  have eq158251 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq158221
       grind)
    | exact superpose eq158221 eq16
    | exact resolve eq16 eq158221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158253 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq158221
       grind)
    | exact superpose eq158221 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq158221
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq158221
       grind)
    | exact resolve eq12 eq158221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158221
  have eq158255 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq158253
  have eq158258 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158255
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq158255
    | exact resolve eq158255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158255
  have eq158286 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158251
       have i₂ := eq25119
       grind)
    | exact superpose eq25119 eq158251
    | exact resolve eq158251 eq25119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25119 eq158251
  have eq158290 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq158286
       have r₂ := eq25404
       grind)
    | exact resolve eq158286 eq25404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25404 eq158286
  have eq158347 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158258
       have i₂ := eq25406
       grind)
    | exact superpose eq25406 eq158258
    | exact resolve eq158258 eq25406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25406
  have eq158385 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq158258
       grind)
    | exact superpose eq158258 eq10
    | exact resolve eq10 eq158258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158258
  have eq158478 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq158347
  have eq158535 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158385
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq158385
    | exact resolve eq158385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158385
  have eq158562 : x = (M.op x y) := by
    first
    | (have r₁ := eq158478
       have r₂ := eq158290
       grind)
    | exact resolve eq158478 eq158290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158290 eq158478
  have eq158563 : y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq158535
       have r₂ := eq12 x y
       grind)
    | exact resolve eq158535 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158535
  have eq158645 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq88 x y
       have i₂ := eq158563
       grind)
    | exact superpose eq158563 eq88
    | (have j0 := eq88 x y
       grind)
    | exact resolve eq88 eq158563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq158673 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq158645
  have eq160204 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq158673
       grind)
    | exact superpose eq158673 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq158673
       grind)
    | exact resolve eq13 eq158673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160206 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq158673
  have eq160207 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq160204
  have eq160208 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq160207
       have r₂ := eq160206
       grind)
    | exact resolve eq160207 eq160206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160207
  have eq160211 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq160208
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq160208
    | exact resolve eq160208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160208
  have eq160213 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq160211
       have i₂ := eq158563
       grind)
    | exact superpose eq158563 eq160211
    | exact resolve eq160211 eq158563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158563 eq160211
  have eq160214 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq160213
       have r₂ := eq160206
       grind)
    | exact resolve eq160213 eq160206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160206 eq160213
  have eq160265 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq160214
       grind)
    | exact superpose eq160214 eq16
    | exact resolve eq16 eq160214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160214
  have eq160276 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq160265
       have i₂ := eq158562
       grind)
    | exact superpose eq158562 eq160265
    | exact resolve eq160265 eq158562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158562 eq160265
  have eq160277 : False := by grind
  exact eq160277

/-- `Equation2862`: `x = ((x ◇ (y ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation2862 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2862 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2862.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq98 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38 x y
       grind)
    | exact superpose eq38 eq16
    | (have j1 := eq38 x y
       grind)
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq455 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42
    | exact resolve eq42 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq487 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq455
    | (have j0 := eq455 X0 X1
       grind)
    | exact resolve eq455 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq819 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq98
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq98
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq98
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq98 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq820 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq819
  have eq4283 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq820
       grind)
    | exact superpose eq820 eq16
    | exact resolve eq16 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4285 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq820
       grind)
    | exact superpose eq820 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq820
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq820
       grind)
    | exact resolve eq13 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq4287 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4285
  have eq4288 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4287
  have eq4290 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4288
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4288
    | exact resolve eq4288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288
  have eq8066 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq487 x y
       have i₂ := eq4290
       grind)
    | exact superpose eq4290 eq487
    | (have j0 := eq487 x y
       grind)
    | exact resolve eq487 eq4290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq4290
  have eq8110 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8066
  have eq8136 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8110
       have r₂ := eq4283
       grind)
    | exact resolve eq8110 eq4283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283 eq8110
  have eq8300 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8136
       grind)
    | exact superpose eq8136 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8136
       grind)
    | exact resolve eq13 eq8136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8302 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq8300
  have eq8303 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8302
  have eq8450 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102 x y
       have i₂ := eq8303
       grind)
    | exact superpose eq8303 eq102
    | (have j0 := eq102 x y
       grind)
    | exact resolve eq102 eq8303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq8303
  have eq8460 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8450
  have eq8461 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8460
  have eq8643 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8461
       grind)
    | exact superpose eq8461 eq16
    | exact resolve eq16 eq8461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq8852 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8643
       have i₂ := eq8136
       grind)
    | exact superpose eq8136 eq8643
    | exact resolve eq8643 eq8136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8136 eq8643
  have eq8853 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8852
  have eq8854 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8853
  have eq9067 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8854
       grind)
    | exact superpose eq8854 eq10
    | exact resolve eq10 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8854
  have eq9142 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9067
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9067
    | exact resolve eq9067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9067
  have eq9143 : x = y := by grind
  clear eq9142
  have eq9335 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
  have eq9336 : False := by grind
  exact eq9336

/-- `Equation2912`: `x = ((y ◇ (x ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation2912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq56 (σ X1) (σ X0)
       grind)
    | exact superpose eq56 eq15
    | (have j1 := eq56 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq56 (τ X1) X0
       grind)
    | exact superpose eq56 eq18
    | (have j1 := eq56 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq56
  have eq267 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq293 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq267
    | (have j0 := eq267 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq663 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
  have eq781 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq663
       have i₂ := eq293 y x
       grind)
    | exact superpose eq293 eq663
    | (have j1 := eq293 (σ x) (σ y)
       grind)
    | (have r₁ := eq663
       have r₂ := eq293 y x
       grind)
    | (have r₁ := eq663
       have r₂ := eq293 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq663
       have r₂ := eq293 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq663 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq663
  have eq782 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq781
  have eq888 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq782
       grind)
    | exact superpose eq782 eq10
    | exact resolve eq10 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq923 : x = y ∨ x = y := by
    first
    | (have i₁ := eq888
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq888
    | exact resolve eq888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq924 : x = y := by grind
  clear eq923
  have eq998 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq924
       grind)
    | exact superpose eq924 eq16
    | exact resolve eq16 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq999 : False := by grind
  exact eq999

/-- `Equation2912`: `x = ((y ◇ (x ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation2912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq94 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq91 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq91 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq180 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq94 (σ X1) (σ X0)
       grind)
    | exact superpose eq94 eq15
    | (have j1 := eq94 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq94 (τ X1) X0
       grind)
    | exact superpose eq94 eq18
    | (have j1 := eq94 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq94
  have eq557 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq592 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq557 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq557
    | (have j0 := eq557 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq557 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq1659 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq180 x y
       grind)
    | exact superpose eq180 eq16
    | (have j1 := eq180 x y
       grind)
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1852 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1659
       have i₂ := eq592 y x
       grind)
    | exact superpose eq592 eq1659
    | (have j1 := eq592 (σ x) (σ y)
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 y x
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1659
       have r₂ := eq592 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1659 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq1659
  have eq1853 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1852
  have eq1894 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1853
       grind)
    | exact superpose eq1853 eq10
    | exact resolve eq10 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq1938 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1894
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1894
    | exact resolve eq1894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq1939 : x = y := by grind
  clear eq1938
  have eq2114 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1939
       grind)
    | exact superpose eq1939 eq16
    | exact resolve eq16 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq2115 : False := by grind
  exact eq2115

/-- `Equation2912`: `x = ((y ◇ (x ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_Equation2912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq50 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq62 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq122 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq157 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq184 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq324 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq60 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq10
    | (have j1 := eq60 X0 X1
       grind)
    | exact resolve eq10 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq343 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq324
    | (have j0 := eq324 X0 X1
       grind)
    | exact resolve eq324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq1082 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq157 (σ X0) (σ X1)
       grind)
    | exact superpose eq157 eq15
    | (have j1 := eq157 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1082 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1082
    | (have j0 := eq1082 X0 X1
       grind)
    | exact resolve eq1082 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1269 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1416 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq343 x y
       grind)
    | exact superpose eq343 eq16
    | (have j1 := eq343 x y
       grind)
    | exact resolve eq16 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq1564 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1740 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1564 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1564
    | (have j0 := eq1564 X0 X1
       grind)
    | exact resolve eq1564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq2098 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq122
    | (have j0 := eq122 X1 (σ X0)
       grind)
    | (have r₁ := eq122 X0 (σ X0)
       have r₂ := eq40 X0
       grind)
    | exact resolve eq122 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq2127 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2098 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2098
    | (have j0 := eq2098 X0 X1
       grind)
    | exact resolve eq2098 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq24706 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1416
       have i₂ := eq1740 y x
       grind)
    | exact superpose eq1740 eq1416
    | (have j1 := eq1740 x y
       grind)
    | (have r₁ := eq1416
       have r₂ := eq1740 y x
       grind)
    | (have r₁ := eq1416
       have r₂ := eq1740 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1416
       have r₂ := eq1740 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1416 eq1740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq1740
  have eq24707 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24706
  have eq24708 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24707
  have eq25477 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq24708
       grind)
    | exact superpose eq24708 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq24708
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq24708
       grind)
    | exact resolve eq12 eq24708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25581 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2127 y X0
       have i₂ := eq24708
       grind)
    | exact superpose eq24708 eq2127
    | (have j0 := eq2127 X0 x
       grind)
    | exact resolve eq2127 eq24708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127 eq24708
  have eq58746 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq25477 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25477
  have eq58842 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq157 x y
       have i₂ := eq58746
       grind)
    | exact superpose eq58746 eq157
    | (have j0 := eq157 x y
       grind)
    | exact resolve eq157 eq58746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq58746
  have eq58853 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58842
  have eq58859 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1269 x y
       grind)
    | (have r₁ := eq58853
       have r₂ := eq1269 x y
       grind)
    | (have r₁ := eq58853
       have r₂ := eq1269 y x
       grind)
    | exact resolve eq58853 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58853
  have eq91666 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq99543 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91666 (τ X1) (τ X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq91666
    | (have j0 := eq91666 (τ X0) (τ X1)
       grind)
    | exact resolve eq91666 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq91666
  have eq99561 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99543 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq99543
    | (have j0 := eq99543 X0 X1
       grind)
    | exact resolve eq99543 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq99543
  have eq99569 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99561 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq99561
    | (have j0 := eq99561 X0 X1
       grind)
    | exact resolve eq99561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99561
  have eq99575 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99569 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq99569
    | (have j0 := eq99569 X0 X1
       grind)
    | (have r₁ := eq99569 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq99569 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99569
  have eq99579 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99575 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq99575
    | (have j0 := eq99575 X0 X1
       grind)
    | exact resolve eq99575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99575
  have eq99581 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99579 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99579
    | (have j0 := eq99579 X0 X1
       grind)
    | exact resolve eq99579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99579
  have eq99583 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99581 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq99581
    | (have j0 := eq99581 X0 X1
       grind)
    | exact resolve eq99581 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99581
  have eq99585 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq99583 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq99583
    | (have j0 := eq99583 X0 X1
       grind)
    | exact resolve eq99583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99583
  have eq99587 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99585 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99585
    | (have j0 := eq99585 X0 X1
       grind)
    | exact resolve eq99585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99585
  have eq99609 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99587 X0 X1
       have i₂ := eq184 X0 X1
       grind)
    | exact superpose eq184 eq99587
    | (have j0 := eq99587 X1 X0
       have j1 := eq184 X1 X0
       grind)
    | (have r₁ := eq99587 X0 X1
       have r₂ := eq184 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq99587 X0 X1
       have r₂ := eq184 (k X1 X0) (k X0 X1)
       grind)
    | exact resolve eq99587 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq99587
  have eq99691 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq99609 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99609
  have eq99700 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq99691 X0 X1
       have j1 := eq1269 X1 X0
       grind)
    | (have r₁ := eq99691 X0 X1
       have r₂ := eq1269 X0 X1
       grind)
    | (have r₁ := eq99691 X0 X1
       have r₂ := eq1269 (M.op X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq99691 X0 X1
       have r₂ := eq1269 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq99691 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269 eq99691
  have eq99739 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99700 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq99700
    | (have j0 := eq99700 (σ X0) (σ X1)
       grind)
    | exact resolve eq99700 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99700
  have eq99771 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99739 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq99739
    | (have j0 := eq99739 X0 X1
       grind)
    | exact resolve eq99739 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99739
  have eq128456 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq25581 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25581
  have eq128487 : (σ (k y x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq99771 y x
       have i₂ := eq128456
       grind)
    | exact superpose eq128456 eq99771
    | (have j0 := eq99771 y x
       grind)
    | (have r₁ := eq99771 y x
       have r₂ := eq128456
       grind)
    | exact resolve eq99771 eq128456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99771 eq128456
  have eq128513 : (σ (k y x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq128487
  have eq128514 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq128513
  have eq128552 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq128514
       grind)
    | exact superpose eq128514 eq16
    | exact resolve eq16 eq128514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128514
  have eq128629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq128552
       have i₂ := eq58859
       grind)
    | exact superpose eq58859 eq128552
    | exact resolve eq128552 eq58859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58859 eq128552
  have eq128648 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq128629
  have eq128649 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq128648
  have eq128655 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq128649
       grind)
    | exact superpose eq128649 eq10
    | exact resolve eq10 eq128649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128649
  have eq129075 : x = y ∨ x = y := by
    first
    | (have i₁ := eq128655
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq128655
    | exact resolve eq128655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128655
  have eq129076 : x = y := by grind
  clear eq129075
  have eq129082 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq129076
       grind)
    | exact superpose eq129076 eq16
    | exact resolve eq16 eq129076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129076
  have eq129083 : False := by grind
  exact eq129083

/-- `Equation2912`: `x = ((y ◇ (x ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq24
  have eq115 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq16
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq332 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq123
    | (have j0 := eq123 (τ X0) (τ X1)
       grind)
    | exact resolve eq123 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq332
    | (have j0 := eq332 X0 X1
       grind)
    | exact resolve eq332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq342 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq339
    | (have j0 := eq339 X0 X1
       grind)
    | exact resolve eq339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq344 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342
    | (have j0 := eq342 X0 X1
       grind)
    | exact resolve eq342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq345 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq346 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq345
    | (have j0 := eq345 X0 X1
       grind)
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq347 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq346
    | (have j0 := eq346 X0 X1
       grind)
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq394 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq124 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq124
    | (have j0 := eq124 (τ X0) (τ X1)
       grind)
    | exact resolve eq124 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq402 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq394
    | (have j0 := eq394 X0 X1
       grind)
    | exact resolve eq394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq405 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq407 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq408 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq407
    | (have j0 := eq407 X0 X1
       grind)
    | exact resolve eq407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq409 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq408
    | (have j0 := eq408 X0 X1
       grind)
    | exact resolve eq408 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq410 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq409
    | (have j0 := eq409 X0 X1
       grind)
    | exact resolve eq409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq455 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq115
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq115 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq456 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq455
  have eq3960 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq456
       grind)
    | exact superpose eq456 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq456
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq456
       grind)
    | exact resolve eq13 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3970 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq456
  have eq3971 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3960
  have eq3972 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3971
       have r₂ := eq3970
       grind)
    | exact resolve eq3971 eq3970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970 eq3971
  have eq3974 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3972
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3972
    | exact resolve eq3972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972
  have eq21445 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3974
       grind)
    | exact superpose eq3974 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3974
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3974
       grind)
    | exact resolve eq12 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3974
  have eq21459 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21445
  have eq21463 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21459
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq21459
    | exact resolve eq21459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21459
  have eq22416 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq21463
       grind)
    | exact superpose eq21463 eq10
    | exact resolve eq10 eq21463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21463
  have eq22567 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22416
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq22416
    | exact resolve eq22416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22416
  have eq22574 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq347 x y
       grind)
    | (have r₁ := eq22567
       have r₂ := eq347 x y
       grind)
    | exact resolve eq22567 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq22567
  have eq23046 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq22574
       grind)
    | exact superpose eq22574 eq10
    | exact resolve eq10 eq22574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22574
  have eq23198 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23046
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23046
    | exact resolve eq23046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23046
  have eq23199 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq410 x y
       grind)
    | (have r₁ := eq23198
       have r₂ := eq410 x y
       grind)
    | exact resolve eq23198 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq23198
  have eq23464 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq23199
       grind)
    | exact superpose eq23199 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq23199
       grind)
    | exact resolve eq13 eq23199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23478 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq23479 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq23464
  have eq23480 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23479
       have r₂ := eq23478
       grind)
    | exact resolve eq23479 eq23478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23479
  have eq24008 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124 x y
       have i₂ := eq23480
       grind)
    | exact superpose eq23480 eq124
    | (have j0 := eq124 x y
       grind)
    | exact resolve eq124 eq23480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq24054 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24008
  have eq138121 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24054
       grind)
    | exact superpose eq24054 eq16
    | exact resolve eq16 eq24054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24054
  have eq138681 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138121
       have i₂ := eq23199
       grind)
    | exact superpose eq23199 eq138121
    | exact resolve eq138121 eq23199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138121
  have eq138684 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq138681
  have eq138685 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq138684
       have r₂ := eq23478
       grind)
    | exact resolve eq138684 eq23478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138684
  have eq138935 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138685
       grind)
    | exact superpose eq138685 eq16
    | exact resolve eq16 eq138685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138937 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq138685
       grind)
    | exact superpose eq138685 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq138685
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq138685
       grind)
    | exact resolve eq12 eq138685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138685
  have eq138940 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq138937
  have eq138943 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138940
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq138940
    | exact resolve eq138940 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138940
  have eq139202 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138935
       have i₂ := eq23199
       grind)
    | exact superpose eq23199 eq138935
    | exact resolve eq138935 eq23199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23199 eq138935
  have eq139206 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq139202
       have r₂ := eq23478
       grind)
    | exact resolve eq139202 eq23478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23478 eq139202
  have eq139924 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138943
       have i₂ := eq23480
       grind)
    | exact superpose eq23480 eq138943
    | exact resolve eq138943 eq23480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23480
  have eq139962 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq138943
       grind)
    | exact superpose eq138943 eq10
    | exact resolve eq10 eq138943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138943
  have eq140050 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq139924
  have eq140107 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139962
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq139962
    | exact resolve eq139962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139962
  have eq140134 : x = (M.op x y) := by
    first
    | (have r₁ := eq140050
       have r₂ := eq139206
       grind)
    | exact resolve eq140050 eq139206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139206 eq140050
  have eq140135 : y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq140107
       have r₂ := eq12 x y
       grind)
    | exact resolve eq140107 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140107
  have eq140476 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123 x y
       have i₂ := eq140135
       grind)
    | exact superpose eq140135 eq123
    | (have j0 := eq123 x y
       grind)
    | exact resolve eq123 eq140135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq140504 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq140476
  have eq145107 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq140504
       grind)
    | exact superpose eq140504 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq140504
       grind)
    | exact resolve eq13 eq140504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145110 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq140504
  have eq145111 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq145107
  have eq145112 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq145111
       have r₂ := eq145110
       grind)
    | exact resolve eq145111 eq145110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145111
  have eq145115 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq145112
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq145112
    | exact resolve eq145112 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145112
  have eq145117 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq145115
       have i₂ := eq140135
       grind)
    | exact superpose eq140135 eq145115
    | exact resolve eq145115 eq140135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140135 eq145115
  have eq145118 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq145117
       have r₂ := eq145110
       grind)
    | exact resolve eq145117 eq145110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145110 eq145117
  have eq145458 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145118
       grind)
    | exact superpose eq145118 eq16
    | exact resolve eq16 eq145118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145118
  have eq145471 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq145458
       have i₂ := eq140134
       grind)
    | exact superpose eq140134 eq145458
    | exact resolve eq145458 eq140134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140134 eq145458
  have eq145472 : False := by grind
  exact eq145472

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation2949 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2949 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq44
    | exact resolve eq44 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq44
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq67 (σ X1) (σ X0)
       grind)
    | exact superpose eq67 eq15
    | (have j1 := eq67 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq67 (τ X1) X0
       grind)
    | exact superpose eq67 eq18
    | (have j1 := eq67 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq67
  have eq195 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq219 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq195
    | (have j0 := eq195 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq595 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq16
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1139 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq595
       have i₂ := eq219 y x
       grind)
    | exact superpose eq219 eq595
    | (have j1 := eq219 (σ x) (σ y)
       grind)
    | (have r₁ := eq595
       have r₂ := eq219 y x
       grind)
    | (have r₁ := eq595
       have r₂ := eq219 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq595
       have r₂ := eq219 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq595 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq595
  have eq1140 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1139
  have eq1328 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1140
       grind)
    | exact superpose eq1140 eq10
    | exact resolve eq10 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1365 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1328
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1328
    | exact resolve eq1328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1366 : x = y := by grind
  clear eq1365
  have eq1571 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1366
       grind)
    | exact superpose eq1366 eq16
    | exact resolve eq16 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq1572 : False := by grind
  exact eq1572

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_Equation2949 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2949 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq43
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq60 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq48 X1
       grind)
    | exact superpose eq48 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq158 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq74 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq10
    | (have j1 := eq74 X0 X1
       grind)
    | exact resolve eq10 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq539 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq527
    | (have j0 := eq527 X0 X1
       grind)
    | exact resolve eq527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq4873 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq539 x y
       grind)
    | exact superpose eq539 eq16
    | (have j1 := eq539 y x
       grind)
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq5219 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60
    | exact resolve eq60 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq5470 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5219 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5219
    | (have j0 := eq5219 X0 X1
       grind)
    | exact resolve eq5219 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5219
  have eq20019 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X1 (σ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq158
    | (have j0 := eq158 X1 (σ X0)
       grind)
    | (have r₁ := eq158 X0 (σ X0)
       have r₂ := eq48 X0
       grind)
    | exact resolve eq158 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq20123 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20019 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20019
    | (have j0 := eq20019 X0 X1
       grind)
    | exact resolve eq20019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20019
  have eq168171 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq4873
       have i₂ := eq5470 y x
       grind)
    | exact superpose eq5470 eq4873
    | (have j1 := eq5470 y x
       grind)
    | (have r₁ := eq4873
       have r₂ := eq5470 y x
       grind)
    | (have r₁ := eq4873
       have r₂ := eq5470 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4873
       have r₂ := eq5470 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4873 eq5470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4873 eq5470
  have eq168172 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq168171
  have eq168173 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq168172
  have eq168436 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq168173
       grind)
    | exact superpose eq168173 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq168173
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq168173
       grind)
    | exact resolve eq12 eq168173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168530 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20123 X0 y
       have i₂ := eq168173
       grind)
    | exact superpose eq168173 eq20123
    | (have j0 := eq20123 X0 x
       grind)
    | exact resolve eq20123 eq168173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20123 eq168173
  have eq187067 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq168436 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168436
  have eq442491 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq168530 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168530
  have eq442504 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq442491
       grind)
    | exact superpose eq442491 eq16
    | exact resolve eq16 eq442491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442491
  have eq442539 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq442504
       have i₂ := eq187067
       grind)
    | exact superpose eq187067 eq442504
    | exact resolve eq442504 eq187067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187067 eq442504
  have eq442558 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq442539
  have eq442559 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq442558
  have eq442561 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq442559
       grind)
    | exact superpose eq442559 eq10
    | exact resolve eq10 eq442559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442559
  have eq443058 : x = y ∨ x = y := by
    first
    | (have i₁ := eq442561
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq442561
    | exact resolve eq442561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442561
  have eq443059 : x = y := by grind
  clear eq443058
  have eq443061 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq443059
       grind)
    | exact superpose eq443059 eq16
    | exact resolve eq16 eq443059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443059
  have eq443062 : False := by grind
  exact eq443062

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_x_x_pxy_Equation2949 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2949 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) ≠ (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op (M.op X0 (M.op X0 X0)) X0) = (k (M.op (M.op X0 (M.op X0 X0)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 (M.op X1 X1)) X1) X1
       have r₂ := eq9 (M.op (M.op X1 (M.op X1 X1)) X1) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k (M.op (M.op X0 (M.op X0 X0)) X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq21 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq45 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq46 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq46 eq15
    | (have j1 := eq46 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 x x
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq208 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq206 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq369 : ∀ X0 : G, (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ≠ (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (σ (M.op (M.op X0 (M.op X0 X0)) X0)) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
    intro X0
    first
    | (have i₁ := eq208 (M.op (M.op X0 (M.op X0 X0)) X0)
       have i₂ := eq22 X0 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq22 eq208
    | (have j0 := eq208 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact resolve eq208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq373 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq208 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq208
    | (have j0 := eq208 (τ X0)
       grind)
    | exact resolve eq208 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq208
  have eq374 : ∀ X0 : G, (σ (M.op (M.op X0 (M.op X0 X0)) X0)) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
    intro X0
    first
    | (have j0 := eq369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq377 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq373
    | (have j0 := eq373 X0
       grind)
    | exact resolve eq373 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq380 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq377 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq377
    | (have j0 := eq377 X0
       grind)
    | exact resolve eq377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq1915 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ X0)) X1) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (σ X0) X1
       have i₂ := eq91 X0 X2 (σ X1)
       grind)
    | exact superpose eq91 eq30
    | (have j1 := eq91 X0 X2 X2
       grind)
    | exact resolve eq30 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1922 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (k (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq91 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1950 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1915 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1915
    | (have j0 := eq1915 X0 X1 X2
       grind)
    | exact resolve eq1915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq2360 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq195
       have i₂ := eq46 x X0 y
       grind)
    | exact superpose eq46 eq195
    | (have j1 := eq46 x X0 y
       grind)
    | exact resolve eq195 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq195
  have eq2361 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2360 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq18798 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1922 (τ X0) (τ X1) X2
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq1922
    | (have j0 := eq1922 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq1922 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq1922
  have eq18895 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18798 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq18798
    | (have j0 := eq18798 X0 X1 X2
       grind)
    | exact resolve eq18798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18798
  have eq18915 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18895 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18895
    | (have j0 := eq18895 X0 X1 X2
       grind)
    | exact resolve eq18895 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18895
  have eq18930 : ∀ X0 X1 X2 : G, (k X0 X2) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18915 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18915
    | (have j0 := eq18915 X0 X1 X2
       grind)
    | exact resolve eq18915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18915
  have eq18944 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X2) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18930 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18930
    | (have j0 := eq18930 X0 X1 X2
       grind)
    | exact resolve eq18930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18930
  have eq18954 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (k X0 X2) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18944 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18944
    | (have j0 := eq18944 X0 X1 X2
       grind)
    | exact resolve eq18944 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18944
  have eq24830 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k X0 X2) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1950 X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq41490 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op (M.op X0 (M.op X0 X0)) X0))
       have i₂ := eq374 X0
       grind)
    | exact superpose eq374 eq9
    | exact resolve eq9 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41517 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41490 X0 X1
       have i₂ := eq374 X0
       grind)
    | exact superpose eq374 eq41490
    | exact resolve eq41490 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41490
  have eq41526 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41517 X0 X1
       have i₂ := eq374 X0
       grind)
    | exact superpose eq374 eq41517
    | exact resolve eq41517 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq41517
  have eq55938 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2361 X0
       grind)
    | exact superpose eq2361 eq13
    | (have j0 := eq13 (σ x) (σ y)
       have j1 := eq2361 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2361 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2361 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2361 X0
       grind)
    | exact resolve eq13 eq2361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361
  have eq56064 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq55938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55938
  have eq56065 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq56064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56064
  have eq56103 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq56065 X0
       have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq56065 X0
       have r₂ := eq12 (σ x) x
       grind)
    | exact resolve eq56065 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56065
  have eq56108 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56103 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq56103
    | (have j0 := eq56103 X0
       grind)
    | exact resolve eq56103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56103
  have eq56148 : ∀ X0 : G, (k x y) = (τ (σ x)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq56108 X0
       grind)
    | exact superpose eq56108 eq10
    | (have j1 := eq56108 X0
       grind)
    | exact resolve eq10 eq56108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56108
  have eq56415 : ∀ X0 : G, x = (k x y) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56148 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq56148
    | (have j0 := eq56148 y
       grind)
    | exact resolve eq56148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56148
  have eq56419 : ∀ X0 : G, x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq56415 X0
       have j1 := eq18954 x y X0
       grind)
    | (have r₁ := eq56415 X0
       have r₂ := eq18954 x y x
       grind)
    | (have r₁ := eq56415 x
       have r₂ := eq18954 x x x
       grind)
    | exact resolve eq56415 eq18954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18954 eq56415
  have eq56471 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq380 x
       have i₂ := eq56419 x
       grind)
    | exact superpose eq56419 eq380
    | (have j0 := eq380 x
       grind)
    | (have r₁ := eq380 x
       have r₂ := eq56419 x
       grind)
    | exact resolve eq380 eq56419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56419
  have eq56616 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq56471
  have eq57478 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq56616
       grind)
    | exact superpose eq56616 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq56616
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq56616
       grind)
    | exact resolve eq13 eq56616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57479 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq57478
  have eq57480 : x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq57479
  have eq57481 : x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq57480
       have r₂ := eq12 x x
       grind)
    | exact resolve eq57480 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57480
  have eq58135 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24830 x y X0
       have i₂ := eq57481
       grind)
    | exact superpose eq57481 eq24830
    | (have j0 := eq24830 x y X0
       grind)
    | exact resolve eq24830 eq57481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24830 eq57481
  have eq58138 : ∀ X0 : G, x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq58135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58135
  have eq64758 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq58138 X0
       grind)
    | exact superpose eq58138 eq16
    | (have j1 := eq58138 X0
       grind)
    | exact resolve eq16 eq58138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58138
  have eq65771 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = (k x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq64758 X0
       have i₂ := eq56616
       grind)
    | exact superpose eq56616 eq64758
    | (have j0 := eq64758 X0
       grind)
    | exact resolve eq64758 eq56616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56616 eq64758
  have eq65772 : ∀ X0 : G, x = (k x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq65771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65771
  have eq65773 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq65772 X0
       have j1 := eq12 x X0
       grind)
    | (have r₁ := eq65772 X0
       have r₂ := eq12 x x
       grind)
    | exact resolve eq65772 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65772
  have eq65924 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq380 x
       have i₂ := eq65773 x
       grind)
    | exact superpose eq65773 eq380
    | (have j0 := eq380 x
       grind)
    | (have r₁ := eq380 x
       have r₂ := eq65773 x
       grind)
    | exact resolve eq380 eq65773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq65773
  have eq66072 : x = (M.op x x) := by grind
  clear eq65924
  have eq67169 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq66072
       grind)
    | exact superpose eq66072 eq9
    | exact resolve eq9 eq66072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67192 : ∀ X0 : G, (M.op (σ (M.op (M.op x x) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41526 x X0
       have i₂ := eq66072
       grind)
    | exact superpose eq66072 eq41526
    | exact resolve eq41526 eq66072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41526
  have eq67210 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67192 X0
       have i₂ := eq66072
       grind)
    | exact superpose eq66072 eq67192
    | exact resolve eq67192 eq66072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67192
  have eq67218 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67169 X0
       have i₂ := eq66072
       grind)
    | exact superpose eq66072 eq67169
    | exact resolve eq67169 eq66072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67169
  have eq67227 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67210 X0
       have i₂ := eq66072
       grind)
    | exact superpose eq66072 eq67210
    | exact resolve eq67210 eq66072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67210
  have eq67233 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67218 X0
       have i₂ := eq66072
       grind)
    | exact superpose eq66072 eq67218
    | exact resolve eq67218 eq66072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66072 eq67218
  have eq68867 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67227 (σ y)
       grind)
    | exact superpose eq67227 eq16
    | exact resolve eq16 eq67227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67227
  have eq69022 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq68867
       have i₂ := eq67233 y
       grind)
    | exact superpose eq67233 eq68867
    | exact resolve eq68867 eq67233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67233 eq68867
  have eq69023 : False := by grind
  exact eq69023

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pxx_pyx_Equation2949 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2949 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) ≠ (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 (M.op X0 X0)) X0)
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X1 X1)) X1)
       have r₂ := eq9 (M.op (M.op X1 (M.op X1 X1)) X1) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq78 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq73 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq109 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq78 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq15
    | exact resolve eq15 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq114
  have eq168 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq168 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq168 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq205 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) X1) X0) = (M.op X0 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 X0 (M.op (M.op X1 (M.op X1 X1)) X1) X2
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq78
    | (have j0 := eq78 X2 X0 X2
       have j1 := eq48 X0 X0
       grind)
    | exact resolve eq78 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq78
  have eq210 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq205 X0 x X2
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq205
    | (have j0 := eq205 X0 x X2
       grind)
    | exact resolve eq205 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq211 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have j0 := eq210 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq292 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq211 X0 (τ X1)
       grind)
    | exact superpose eq211 eq17
    | (have j1 := eq211 X0 x
       grind)
    | exact resolve eq17 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq211
  have eq352 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq172 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq172
    | exact resolve eq172 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq386 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq125 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq125 eq352
    | exact resolve eq352 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq399 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq386
    | exact resolve eq386 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq402 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1
       have i₂ := eq125 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq125 eq399
    | exact resolve eq399 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq399
  have eq404 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq402
    | exact resolve eq402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq4186 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq292 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq292
    | (have j0 := eq292 X1 X1
       grind)
    | exact resolve eq292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq4310 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4186 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4186
    | (have j0 := eq4186 X0 X1
       grind)
    | exact resolve eq4186 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4186
  have eq12698 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq174 X0 X1
       grind)
    | exact superpose eq174 eq10
    | (have j1 := eq174 X0 X1
       grind)
    | exact resolve eq10 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq12788 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12698 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12698
    | (have j0 := eq12698 X0 X1
       grind)
    | exact resolve eq12698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12698
  have eq13376 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12788 X0 (σ X1)
       grind)
    | exact superpose eq12788 eq15
    | (have j1 := eq12788 X0 X1
       grind)
    | exact resolve eq15 eq12788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12788
  have eq15462 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13376 x y
       grind)
    | exact superpose eq13376 eq16
    | (have j1 := eq13376 x x
       grind)
    | exact resolve eq16 eq13376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13376
  have eq15671 : x = (M.op x x) := by
    first
    | (have j1 := eq4310 x x
       grind)
    | (have r₁ := eq15462
       have r₂ := eq4310 y x
       grind)
    | exact resolve eq15462 eq4310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4310 eq15462
  have eq16140 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq15671
       grind)
    | exact superpose eq15671 eq9
    | exact resolve eq9 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16162 : ∀ X0 : G, (M.op (σ (M.op (M.op x x) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq404 x X0
       have i₂ := eq15671
       grind)
    | exact superpose eq15671 eq404
    | exact resolve eq404 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq16195 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16162 X0
       have i₂ := eq15671
       grind)
    | exact superpose eq15671 eq16162
    | exact resolve eq16162 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16162
  have eq16208 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16140 X0
       have i₂ := eq15671
       grind)
    | exact superpose eq15671 eq16140
    | exact resolve eq16140 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16140
  have eq16219 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16195 X0
       have i₂ := eq15671
       grind)
    | exact superpose eq15671 eq16195
    | exact resolve eq16195 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16195
  have eq16230 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16208 X0
       have i₂ := eq15671
       grind)
    | exact superpose eq15671 eq16208
    | exact resolve eq16208 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15671 eq16208
  have eq18582 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16219 (σ y)
       grind)
    | exact superpose eq16219 eq16
    | exact resolve eq16 eq16219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16219
  have eq18723 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq18582
       have i₂ := eq16230 y
       grind)
    | exact superpose eq16230 eq18582
    | exact resolve eq18582 eq16230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16230 eq18582
  have eq18724 : False := by grind
  exact eq18724

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation2949 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2949 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq206 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq207 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq206 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq213 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq207 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq207 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq207 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq223 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq213 (σ X0)
       grind)
    | exact superpose eq213 eq15
    | exact resolve eq15 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq223 X0
       have i₂ := eq213 X0
       grind)
    | exact superpose eq213 eq223
    | exact resolve eq223 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq322 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq9
    | exact resolve eq9 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq322 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq322
    | exact resolve eq322 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq563 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 X1
       have i₂ := eq232 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq232 eq527
    | exact resolve eq527 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq580 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq563
    | exact resolve eq563 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq582 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq232 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq232 eq580
    | exact resolve eq580 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq584 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq582
    | exact resolve eq582 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq659 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq74 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq74 eq15
    | (have j1 := eq74 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq691 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq659 X0 X1 X2
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq659
    | (have j0 := eq659 X0 X1 X2
       grind)
    | exact resolve eq659 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq6729 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 X0 X0
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq6931 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6729 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6729
    | (have j0 := eq6729 X0 X0
       grind)
    | exact resolve eq6729 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6729
  have eq78091 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq691 X0 X1 X2
       grind)
    | exact superpose eq691 eq10
    | (have j1 := eq691 X0 X1 X2
       grind)
    | exact resolve eq10 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq78814 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78091 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78091
    | (have j0 := eq78091 X0 X1 X2
       grind)
    | exact resolve eq78091 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78091
  have eq162487 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq6931 X2 X0
       grind)
    | exact superpose eq6931 eq324
    | (have j0 := eq324 X0 X1
       have j1 := eq6931 X2 X0
       grind)
    | exact resolve eq324 eq6931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq6931
  have eq162635 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq162487 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162487
  have eq244491 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq78814 x y X0
       grind)
    | exact superpose eq78814 eq16
    | (have j1 := eq78814 x y X0
       grind)
    | exact resolve eq16 eq78814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78814
  have eq244497 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op X0 X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq244491 X0
       have j1 := eq162635 y X0 X0
       grind)
    | (have r₁ := eq244491 X0
       have r₂ := eq162635 y x x
       grind)
    | exact resolve eq244491 eq162635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162635 eq244491
  have eq244527 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213 (σ y)
       have i₂ := eq244497 (σ y)
       grind)
    | exact superpose eq244497 eq213
    | (have j1 := eq244497 (σ y)
       grind)
    | exact resolve eq213 eq244497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq244497
  have eq244701 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq244527
  have eq244793 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq244701
       have i₂ := eq232 y
       grind)
    | exact superpose eq232 eq244701
    | exact resolve eq244701 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq244701
  have eq244837 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq323 y X0
       have i₂ := eq244793
       grind)
    | exact superpose eq244793 eq323
    | (have j0 := eq323 y X0
       grind)
    | (have r₁ := eq323 y x
       have r₂ := eq244793
       grind)
    | exact resolve eq323 eq244793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq244873 : (M.op y y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq244793
       grind)
    | exact superpose eq244793 eq10
    | exact resolve eq10 eq244793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244793
  have eq244934 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq244837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244837
  have eq244955 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq244873
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq244873
    | exact resolve eq244873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244873
  have eq245029 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq244955
       grind)
    | exact superpose eq244955 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq244955
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq244955
       grind)
    | exact resolve eq12 eq244955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244955
  have eq245246 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq245029 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245029
  have eq245861 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq244934 (σ X0)
       grind)
    | exact superpose eq244934 eq15
    | exact resolve eq15 eq244934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244934
  have eq255278 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq245861 x
       grind)
    | exact superpose eq245861 eq16
    | exact resolve eq16 eq245861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245861
  have eq255655 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq255278
       have i₂ := eq245246 x
       grind)
    | exact superpose eq245246 eq255278
    | exact resolve eq255278 eq245246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245246 eq255278
  have eq255695 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq255655
  have eq255696 : x = (M.op x x) := by grind
  clear eq255695
  have eq255705 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq255696
       grind)
    | exact superpose eq255696 eq9
    | exact resolve eq9 eq255696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255768 : ∀ X0 : G, (M.op (σ (M.op (M.op x x) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq584 x X0
       have i₂ := eq255696
       grind)
    | exact superpose eq255696 eq584
    | exact resolve eq584 eq255696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq256122 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq255768 X0
       have i₂ := eq255696
       grind)
    | exact superpose eq255696 eq255768
    | exact resolve eq255768 eq255696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255768
  have eq256156 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq255705 X0
       have i₂ := eq255696
       grind)
    | exact superpose eq255696 eq255705
    | exact resolve eq255705 eq255696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255705
  have eq256288 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq256122 X0
       have i₂ := eq255696
       grind)
    | exact superpose eq255696 eq256122
    | exact resolve eq256122 eq255696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256122
  have eq256310 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq256156 X0
       have i₂ := eq255696
       grind)
    | exact superpose eq255696 eq256156
    | exact resolve eq256156 eq255696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255696 eq256156
  have eq260823 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256288 (σ y)
       grind)
    | exact superpose eq256288 eq16
    | exact resolve eq16 eq256288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256288
  have eq261457 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq260823
       have i₂ := eq256310 y
       grind)
    | exact superpose eq256310 eq260823
    | exact resolve eq260823 eq256310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256310 eq260823
  have eq261458 : False := by grind
  exact eq261458

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pyx_Equation2949 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2949 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq78 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq73 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq74 X0 X1 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq74 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq74 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq109 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq78 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq15
    | exact resolve eq15 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq175 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq179 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq179 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq259 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0
       have i₂ := eq79 X0 X0 X1
       grind)
    | exact superpose eq79 eq110
    | (have j1 := eq79 X0 X0 X1
       grind)
    | exact resolve eq110 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq110
  have eq275 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq303 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq275 X0 (τ X1)
       grind)
    | exact superpose eq275 eq17
    | (have j1 := eq275 X0 X1
       grind)
    | exact resolve eq17 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq275
  have eq343 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq175
    | exact resolve eq175 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq375 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq343 X0 X1
       have i₂ := eq125 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq125 eq343
    | exact resolve eq343 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq389 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq375
    | exact resolve eq375 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq392 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq125 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq125 eq389
    | exact resolve eq389 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq389
  have eq394 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq392 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq392
    | exact resolve eq392 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq9600 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq303 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq303
    | (have j0 := eq303 X1 X1
       grind)
    | exact resolve eq303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq9765 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9600 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9600
    | (have j0 := eq9600 X0 X1
       grind)
    | exact resolve eq9600 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9600
  have eq26239 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq10
    | (have j1 := eq182 X0 X1
       grind)
    | exact resolve eq10 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq26356 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26239 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26239
    | (have j0 := eq26239 X0 X1
       grind)
    | exact resolve eq26239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26239
  have eq27156 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq26356 X0 (σ X1)
       grind)
    | exact superpose eq26356 eq15
    | (have j1 := eq26356 X0 X1
       grind)
    | exact resolve eq15 eq26356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26356
  have eq30339 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27156 x y
       grind)
    | exact superpose eq27156 eq16
    | (have j1 := eq27156 x x
       grind)
    | exact resolve eq16 eq27156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27156
  have eq30651 : x = (M.op x x) := by
    first
    | (have j1 := eq9765 x x
       grind)
    | (have r₁ := eq30339
       have r₂ := eq9765 y x
       grind)
    | exact resolve eq30339 eq9765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9765 eq30339
  have eq31650 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq30651
       grind)
    | exact superpose eq30651 eq9
    | exact resolve eq9 eq30651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31686 : ∀ X0 : G, (M.op (σ (M.op (M.op x x) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq394 x X0
       have i₂ := eq30651
       grind)
    | exact superpose eq30651 eq394
    | exact resolve eq394 eq30651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq31752 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31686 X0
       have i₂ := eq30651
       grind)
    | exact superpose eq30651 eq31686
    | exact resolve eq31686 eq30651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31686
  have eq31770 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31650 X0
       have i₂ := eq30651
       grind)
    | exact superpose eq30651 eq31650
    | exact resolve eq31650 eq30651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31650
  have eq31796 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31752 X0
       have i₂ := eq30651
       grind)
    | exact superpose eq30651 eq31752
    | exact resolve eq31752 eq30651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31752
  have eq31810 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31770 X0
       have i₂ := eq30651
       grind)
    | exact superpose eq30651 eq31770
    | exact resolve eq31770 eq30651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30651 eq31770
  have eq35536 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31796 (σ y)
       grind)
    | exact superpose eq31796 eq16
    | exact resolve eq16 eq31796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31796
  have eq35756 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq35536
       have i₂ := eq31810 y
       grind)
    | exact superpose eq31810 eq35536
    | exact resolve eq35536 eq31810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31810 eq35536
  have eq35757 : False := by grind
  exact eq35757
