import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X2 X3) (M.op X1 X0))) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq108 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq148 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X1 X1) X1) := by
    intro X1
    first
    | (have i₁ := eq147 X1
       have i₂ := eq31 X1 X1
       grind)
    | exact superpose eq31 eq147
    | exact resolve eq147 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq147
  have eq163 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq108 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq199 : ∀ X1 X3 X4 : G, (M.op (M.op X1 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq30 X3 x (M.op (M.op x x) (M.op X1 X1)) X4
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq238 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq163 X1 (M.op x (M.op x x))
       have i₂ := eq199 x x x
       grind)
    | exact superpose eq199 eq163
    | exact resolve eq163 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq199
  have eq333 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X1
       have i₂ := eq106 X0 X1
       grind)
    | (have i₁ := eq148 X1
       have i₂ := eq106 (M.op X1 X1) X1
       grind)
    | exact superpose eq106 eq148
    | (have j1 := eq106 X0 X1
       grind)
    | exact resolve eq148 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq340 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq597 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq744 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (k X0 X3) ∨ (M.op X1 (M.op (M.op X2 X1) (M.op X3 X0))) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq148 X1
       have i₂ := eq100 X0 X1 X2 X3
       grind)
    | (have i₁ := eq148 X1
       have i₂ := eq100 (M.op X1 X1) X1 X2 X3
       grind)
    | exact superpose eq100 eq148
    | (have j1 := eq100 X0 X3 X2 X1
       grind)
    | exact resolve eq148 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq148
  have eq751 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X3 X0))) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq744 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq2345 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 X0 (M.op X0 X0) X2 X1
       have i₂ := eq238 X0 X0
       grind)
    | exact superpose eq238 eq120
    | exact resolve eq120 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2808 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X1
       have i₂ := eq2345 X1 X2 X0
       grind)
    | exact superpose eq2345 eq115
    | exact resolve eq115 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq2809 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq238 X1 X3
       have i₂ := eq2345 X1 X2 X0
       grind)
    | exact superpose eq2345 eq238
    | exact resolve eq238 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq2836 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq120 (M.op X0 X1) X1 X3 X2
       have i₂ := eq2345 X1 X1 X0
       grind)
    | exact superpose eq2345 eq120
    | exact resolve eq120 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2871 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2836 X0 X1 x x
       have i₂ := eq120 X1 X1 x x
       grind)
    | exact superpose eq120 eq2836
    | exact resolve eq2836 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq2836
  have eq4591 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2808 X0 (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) (M.op X1 X2)
       have i₂ := eq2809 X3 X2 (M.op X0 (M.op X1 X2)) X1
       grind)
    | exact superpose eq2809 eq2808
    | exact resolve eq2808 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808 eq2809
  have eq4643 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4591 X0 X1 X2 X3
       have i₂ := eq2871 (M.op X3 (M.op X0 (M.op X1 X2))) X2
       grind)
    | exact superpose eq2871 eq4591
    | exact resolve eq4591 eq2871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871 eq4591
  have eq6813 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4643 (M.op x x) X1 X0 x
       have i₂ := eq751 X0 x x X1
       grind)
    | exact superpose eq751 eq4643
    | (have j1 := eq751 X0 X1 x X1
       grind)
    | exact resolve eq4643 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq4643
  have eq6928 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq6813 X0 X1
       have j1 := eq597 X0 X1
       grind)
    | (have r₁ := eq6813 X0 X1
       have r₂ := eq597 X0 X1
       grind)
    | (have r₁ := eq6813 X0 X0
       have r₂ := eq597 X0 X0
       grind)
    | exact resolve eq6813 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq6813
  have eq7066 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq6928 (σ X0) (σ X1)
       grind)
    | exact superpose eq6928 eq15
    | exact resolve eq15 eq6928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7076 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7066 X0 X1
       have i₂ := eq6928 X0 X1
       grind)
    | exact superpose eq6928 eq7066
    | exact resolve eq7066 eq6928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6928 eq7066
  have eq7193 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7076 y x
       grind)
    | exact superpose eq7076 eq16
    | (have r₁ := eq16
       have r₂ := eq7076 y x
       grind)
    | exact resolve eq16 eq7076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7076
  have eq7226 : False := by grind
  exact eq7226

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (M.op y y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq104 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq100
    | exact resolve eq100 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq104
    | exact resolve eq104 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq104
  have eq142 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq245 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq245 eq14
    | exact resolve eq14 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq595 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq592
    | exact resolve eq592 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq598 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq589 X0 X1 X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq589
    | exact resolve eq589 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq605 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq576 X0 X1 X2 X3 X4
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq576
    | exact resolve eq576 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq638 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq51
    | exact resolve eq51 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1608 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq522 (M.op x sF4) (M.op x sF4)
       have i₂ := eq14 (M.op x sF4) sF4 x
       grind)
    | exact superpose eq14 eq522
    | exact resolve eq522 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1618 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1608 X0
       have i₂ := eq54 X0 sF4
       grind)
    | exact superpose eq54 eq1608
    | exact resolve eq1608 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608
  have eq1758 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq552 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq552 X0 X0 X0
       grind)
    | exact superpose eq552 eq552
    | exact resolve eq552 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1779 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq552 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq552 X0 X0 X0
       grind)
    | exact superpose eq552 eq552
    | exact resolve eq552 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1810 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq552 X0 X0 X0
       grind)
    | exact superpose eq552 eq14
    | exact resolve eq14 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq552 X0 X0 X0
       grind)
    | exact superpose eq552 eq51
    | exact resolve eq51 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1813 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq552 X0 X0 X0
       grind)
    | exact superpose eq552 eq52
    | exact resolve eq52 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1820 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq510 (M.op x (M.op x x))
       have i₂ := eq552 x x x
       grind)
    | exact superpose eq552 eq510
    | exact resolve eq510 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq1823 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq585 (M.op x (M.op x x)) x
       have i₂ := eq552 x x x
       grind)
    | exact superpose eq552 eq585
    | exact resolve eq585 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq2094 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq519 X0
       have i₂ := eq1812 X0
       grind)
    | exact superpose eq1812 eq519
    | exact resolve eq519 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2121 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1812 eq522
    | exact resolve eq522 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2132 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq522 eq2121
    | exact resolve eq2121 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq2121
  have eq2169 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq638 eq2094
    | exact resolve eq2094 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq2094
  have eq2337 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1813 X0
       have i₂ := eq1812 X0
       grind)
    | exact superpose eq1812 eq1813
    | exact resolve eq1813 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq2497 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1820 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1820
    | exact resolve eq1820 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq2541 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2497 X0 X1
       have i₂ := eq1812 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1812 eq2497
    | exact resolve eq2497 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq2556 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2541 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2541
    | exact resolve eq2541 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq2734 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq27 eq1823
    | (have j0 := eq1823 (σ y) (σ x)
       grind)
    | exact resolve eq1823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823
  have eq2794 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2734
       have i₂ := eq1812 sF3
       grind)
    | exact superpose eq1812 eq2734
    | exact resolve eq2734 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq5663 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq575
    | exact resolve eq575 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq5720 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq245 eq5663
    | exact resolve eq5663 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5663
  have eq5951 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq598 X0 X1 X2 X3
       have i₂ := eq595 X0 X1
       grind)
    | exact superpose eq595 eq598
    | exact resolve eq598 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq5952 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2337 eq5951
    | exact resolve eq5951 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5951
  have eq6122 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5952 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq552 x X1 X0
       grind)
    | exact superpose eq552 eq5952
    | exact resolve eq5952 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq6145 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5952 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq5952
    | exact resolve eq5952 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6198 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq5952 X0 (M.op X1 X2) (M.op X1 X2) X0
       grind)
    | exact superpose eq5952 eq14
    | exact resolve eq14 eq5952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5952
  have eq7067 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq605 X0 X1 X2 X3 X4
       have i₂ := eq595 X0 X1
       grind)
    | exact superpose eq595 eq605
    | exact resolve eq605 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq605
  have eq7068 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq2337 eq7067
    | exact resolve eq7067 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067
  have eq7188 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7068 X0 (M.op X0 (M.op X0 X0)) X2 X3 x
       have i₂ := eq519 X0
       grind)
    | exact superpose eq519 eq7068
    | exact resolve eq7068 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq7068
  have eq28888 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq575 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1810 X0 X0 X1
       grind)
    | exact superpose eq1810 eq575
    | exact resolve eq575 eq1810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28977 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28888 X0 X1 x x x
       have i₂ := eq575 X0 X0 x x x
       grind)
    | exact superpose eq575 eq28888
    | exact resolve eq28888 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq28888
  have eq29808 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5720 eq1810
    | exact resolve eq1810 eq5720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810 eq5720
  have eq29847 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1618 eq29808
    | exact resolve eq29808 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq29808
  have eq29850 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2337 eq29847
    | exact resolve eq29847 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337 eq29847
  have eq42934 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2556 eq14
    | exact resolve eq14 eq2556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556
  have eq43724 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1758 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1758
    | (have j0 := eq1758 y x X0
       grind)
    | exact resolve eq1758 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq46038 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq1779
    | (have j0 := eq1779 (σ y) X0 (σ x)
       grind)
    | exact resolve eq1779 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46606 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq46038 X0
       have i₂ := eq1812 sF3
       grind)
    | exact superpose eq1812 eq46038
    | exact resolve eq46038 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq46038
  have eq68157 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq43724 y
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq43724
    | exact resolve eq43724 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq43724
  have eq68300 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq68157
       have i₂ := eq28977 (M.op y x) y
       grind)
    | exact superpose eq28977 eq68157
    | exact resolve eq68157 eq28977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68157
  have eq68336 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq68300
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq68300
    | exact resolve eq68300 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq68300
  have eq68353 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq42934 eq68336
    | exact resolve eq68336 eq42934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42934 eq68336
  have eq96124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6145 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq1779 X0 x X1
       grind)
    | exact superpose eq1779 eq6145
    | exact resolve eq6145 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq97001 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6145 eq96124
    | exact resolve eq96124 eq6145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96124
  have eq108631 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6122 eq6198
    | exact resolve eq6198 eq6122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6122
  have eq108656 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X3)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6198 eq6145
    | exact resolve eq6145 eq6198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq108866 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6145 eq108656
    | exact resolve eq108656 eq6145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108656
  have eq112343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6145 X2 (M.op X1 X0) (M.op (M.op x x) (M.op X1 X1)) X3
       have i₂ := eq7188 X0 x x X1
       grind)
    | exact superpose eq7188 eq6145
    | exact resolve eq6145 eq7188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq112380 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6145 eq112343
    | exact resolve eq112343 eq6145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6145 eq112343
  have eq165507 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq46606 eq108631
    | exact resolve eq108631 eq46606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46606 eq108631
  have eq166257 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq165507
       have i₂ := eq112380 sF2 sF2 (M.op sF4 sF4)
       grind)
    | exact superpose eq112380 eq165507
    | exact resolve eq165507 eq112380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165507
  have eq166601 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq245 eq166257
    | exact resolve eq166257 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq166257
  have eq166784 : (σ y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2794 eq166601
    | exact resolve eq166601 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794 eq166601
  have eq167158 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq166784
       have i₂ := eq112380 sF2 sF0 (M.op sF3 sF4)
       grind)
    | exact superpose eq112380 eq166784
    | exact resolve eq166784 eq112380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166784
  have eq262526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq68353 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq68353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68353
  have eq262527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq262526
    | exact resolve eq262526 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262526
  have eq262538 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq262527
       have r₂ := eq28
       grind)
    | exact resolve eq262527 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262527
  have eq262561 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq262538 eq29850
    | exact resolve eq29850 eq262538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29850
  have eq262721 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq262538 eq254
    | exact resolve eq254 eq262538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq262794 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ y) (σ x)))) X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq262538 eq108866
    | exact resolve eq108866 eq262538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262808 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by grind
  have eq262820 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq108866 eq262794
    | exact resolve eq262794 eq108866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108866 eq262794
  have eq262856 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq262721
       have i₂ := eq97001 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq97001 eq262721
    | exact resolve eq262721 eq97001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262721
  have eq262957 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq262561
       have i₂ := eq97001 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq97001 eq262561
    | exact resolve eq262561 eq97001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97001 eq262561
  have eq262988 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq262856
       have i₂ := eq112380 sF2 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq112380 eq262856
    | exact resolve eq262856 eq112380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262856
  have eq263046 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq262957
       have i₂ := eq112380 sF2 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq112380 eq262957
    | exact resolve eq262957 eq112380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112380 eq262957
  have eq263052 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq167158 eq262988
    | exact resolve eq262988 eq167158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262988
  have eq263074 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq167158 eq263046
    | exact resolve eq263046 eq167158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167158 eq263046
  have eq263079 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq262538 eq263052
    | exact resolve eq263052 eq262538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262538 eq263052
  have eq263346 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq263079
  have eq263462 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq263346
       have r₂ := eq262808
       grind)
    | exact resolve eq263346 eq262808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262808 eq263346
  have eq270455 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq262820 eq263462
    | exact resolve eq263462 eq262820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262820 eq263462
  have eq271062 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq270455
  have eq271623 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq271062 eq51
    | exact resolve eq51 eq271062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq271062
  have eq284023 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq271623 eq263074
    | exact resolve eq263074 eq271623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263074 eq271623
  have eq284160 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq284023
  have eq284312 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq284160 eq142
    | exact resolve eq142 eq284160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq284160
  have eq284726 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq284312
    | exact resolve eq284312 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284312
  have eq284727 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq284726
  have eq285113 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28977 y y
       have i₂ := eq284727
       grind)
    | exact superpose eq284727 eq28977
    | exact resolve eq28977 eq284727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28977 eq284727
  have eq285156 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq285113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq285113
    | exact resolve eq285113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285113
  have eq285420 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq285156 eq30
    | exact resolve eq30 eq285156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq285156
  have eq285774 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq285420
    | exact resolve eq285420 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq285420
  have eq285775 : x = (M.op x y) ∨ x = y := by grind
  clear eq285774
  have eq285811 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq285775 eq21
    | exact resolve eq21 eq285775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285928 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq285775 eq2132
    | exact resolve eq2132 eq285775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132 eq285775
  have eq286289 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq285928
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq285928
    | exact resolve eq285928 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285928
  have eq286359 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq285811
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq285811
    | exact resolve eq285811 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285811
  have eq286412 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq286359 eq27
    | exact resolve eq27 eq286359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286359
  have eq286751 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2169 y
       have i₂ := eq286289
       grind)
    | exact superpose eq286289 eq2169
    | exact resolve eq2169 eq286289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169 eq286289
  have eq286969 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq286751
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq286751
    | exact resolve eq286751 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286751
  have eq287074 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq286969
    | exact resolve eq286969 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286969
  have eq287912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq287074 eq286412
    | exact resolve eq286412 eq287074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286412 eq287074
  have eq288014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq287912
  have eq288064 : x = y := by
    first
    | (have r₁ := eq288014
       have r₂ := eq28
       grind)
    | exact resolve eq288014 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288014
  have eq288091 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq288064
       grind)
    | exact superpose eq288064 eq19
    | exact resolve eq19 eq288064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq288092 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq288064
       grind)
    | exact superpose eq288064 eq25
    | exact resolve eq25 eq288064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq288064
  have eq288620 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq288092
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq288092
    | exact resolve eq288092 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq288092
  have eq288699 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq288620 eq27
    | exact resolve eq27 eq288620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq288620
  have eq289935 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq288699 eq72
    | exact resolve eq72 eq288699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq288699
  have eq290374 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq289935
       have i₂ := eq288091
       grind)
    | exact superpose eq288091 eq289935
    | exact resolve eq289935 eq288091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288091 eq289935
  have eq290600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq290374 eq15
    | exact resolve eq15 eq290374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290374
  have eq290958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq290600
    | exact resolve eq290600 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq290600
  have eq291085 : False := by grind
  exact eq291085

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq78 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq45
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq45 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq25 eq37
  have eq109 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq105
    | exact resolve eq105 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq109
    | exact resolve eq109 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq109
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq16
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq78
    | (have j0 := eq78 (σ x) (σ y)
       grind)
    | exact resolve eq78 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq98
  have eq996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq995
    | exact resolve eq995 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq999 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq996
       have r₂ := eq28
       grind)
    | exact resolve eq996 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1001 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq999 eq129
    | exact resolve eq129 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq999
  have eq1016 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1001
    | exact resolve eq1001 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1001
  have eq1017 : x = (M.op y y) := by grind
  clear eq1016
  have eq1029 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq1017
       grind)
    | exact superpose eq1017 eq111
    | exact resolve eq111 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1035 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1
       have i₂ := eq1017
       grind)
    | exact superpose eq1017 eq14
    | exact resolve eq14 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1045 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1029
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1029
    | exact resolve eq1029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1052 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq1045 eq14
    | exact resolve eq14 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1556 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq1035 (M.op x x) x
       have i₂ := eq579 x x
       grind)
    | exact superpose eq579 eq1035
    | exact resolve eq1035 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1565 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq1556
       have i₂ := eq54 x x
       grind)
    | exact superpose eq54 eq1556
    | exact resolve eq1556 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1670 : x = (M.op x y) := by
    first
    | (have i₁ := eq497 x
       have i₂ := eq1565
       grind)
    | exact superpose eq1565 eq497
    | exact resolve eq497 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1688 : x = (M.op x y) := by
    first
    | (have i₁ := eq1670
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1670
    | exact resolve eq1670 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1670
  have eq1690 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1688 eq21
    | exact resolve eq21 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1688
  have eq1725 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1690
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1690
    | exact resolve eq1690 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1690
  have eq1729 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1725 eq27
    | exact resolve eq27 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2015 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1725 eq1052
    | exact resolve eq1052 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq1725
  have eq2306 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2015 (M.op sF1 sF1) x
       have i₂ := eq579 sF1 x
       grind)
    | exact superpose eq579 eq2015
    | exact resolve eq2015 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq2015
  have eq2320 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2306
       have i₂ := eq54 sF1 sF1
       grind)
    | exact superpose eq54 eq2306
    | exact resolve eq2306 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2306
  have eq2360 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2320 eq497
    | exact resolve eq497 eq2320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq2320
  have eq2383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1729 eq2360
    | exact resolve eq2360 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729 eq2360
  have eq2388 : False := by grind
  exact eq2388

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (M.op y y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq104 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq100
    | exact resolve eq100 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq104
    | exact resolve eq104 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq104
  have eq142 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq245 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq245 eq14
    | exact resolve eq14 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq595 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq590
    | exact resolve eq590 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq597 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq588 X0 X1 X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq588
    | exact resolve eq588 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq604 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq575 X0 X1 X2 X3 X4
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq575
    | exact resolve eq575 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq637 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq51
    | exact resolve eq51 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1593 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq522 (M.op x sF4) (M.op x sF4)
       have i₂ := eq14 (M.op x sF4) sF4 x
       grind)
    | exact superpose eq14 eq522
    | exact resolve eq522 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1602 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1593 X0
       have i₂ := eq54 X0 sF4
       grind)
    | exact superpose eq54 eq1593
    | exact resolve eq1593 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1738 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq551 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq551 X0 X0 X0
       grind)
    | exact superpose eq551 eq551
    | exact resolve eq551 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1759 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq551 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq551 X0 X0 X0
       grind)
    | exact superpose eq551 eq551
    | exact resolve eq551 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1790 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq551 X0 X0 X0
       grind)
    | exact superpose eq551 eq14
    | exact resolve eq14 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1792 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq551 X0 X0 X0
       grind)
    | exact superpose eq551 eq51
    | exact resolve eq51 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq551 X0 X0 X0
       grind)
    | exact superpose eq551 eq52
    | exact resolve eq52 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1801 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq510 (M.op x (M.op x x))
       have i₂ := eq551 x x x
       grind)
    | exact superpose eq551 eq510
    | exact resolve eq510 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq1804 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq584 (M.op x (M.op x x)) x
       have i₂ := eq551 x x x
       grind)
    | exact superpose eq551 eq584
    | exact resolve eq584 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq2080 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq519 X0
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq519
    | exact resolve eq519 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2107 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1792 eq522
    | exact resolve eq522 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2117 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq522 eq2107
    | exact resolve eq2107 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq2107
  have eq2153 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq637 eq2080
    | exact resolve eq2080 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq2080
  have eq2370 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1793 X0
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq1793
    | exact resolve eq1793 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq2527 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1801 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1801
    | exact resolve eq1801 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq2571 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2527 X0 X1
       have i₂ := eq1792 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1792 eq2527
    | exact resolve eq2527 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2586 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2571 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2571
    | exact resolve eq2571 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq2766 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq27 eq1804
    | (have j0 := eq1804 (σ y) (σ x)
       grind)
    | exact resolve eq1804 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804
  have eq2826 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2766
       have i₂ := eq1792 sF3
       grind)
    | exact superpose eq1792 eq2766
    | exact resolve eq2766 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq5870 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq574
    | exact resolve eq574 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq5927 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq245 eq5870
    | exact resolve eq5870 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5870
  have eq6067 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq597 X0 X1 X2 X3
       have i₂ := eq595 X0 X1
       grind)
    | exact superpose eq595 eq597
    | exact resolve eq597 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq6239 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6067 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq551 x X1 X0
       grind)
    | exact superpose eq551 eq6067
    | exact resolve eq6067 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq6263 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6067 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq6067
    | exact resolve eq6067 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6317 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq6067 X0 (M.op X1 X2) (M.op X1 X2) X0
       grind)
    | exact superpose eq6067 eq14
    | exact resolve eq14 eq6067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6067
  have eq7169 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq604 X0 X1 X2 X3 X4
       have i₂ := eq595 X0 X1
       grind)
    | exact superpose eq595 eq604
    | exact resolve eq604 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq604
  have eq7377 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7169 X0 (M.op X0 (M.op X0 X0)) X2 X3 x
       have i₂ := eq519 X0
       grind)
    | exact superpose eq519 eq7169
    | exact resolve eq7169 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq7169
  have eq28763 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq574 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1790 X0 X0 X1
       grind)
    | exact superpose eq1790 eq574
    | exact resolve eq574 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28849 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28763 X0 X1 x x x
       have i₂ := eq574 X0 X0 x x x
       grind)
    | exact superpose eq574 eq28763
    | exact resolve eq28763 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq28763
  have eq30030 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5927 eq1790
    | exact resolve eq1790 eq5927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790 eq5927
  have eq30070 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1602 eq30030
    | exact resolve eq30030 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602 eq30030
  have eq30073 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2370 eq30070
    | exact resolve eq30070 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370 eq30070
  have eq42720 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2586 eq14
    | exact resolve eq14 eq2586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586
  have eq43494 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1738 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1738
    | (have j0 := eq1738 y x X0
       grind)
    | exact resolve eq1738 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq45437 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq1759
    | (have j0 := eq1759 (σ y) X0 (σ x)
       grind)
    | exact resolve eq1759 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46002 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq45437 X0
       have i₂ := eq1792 sF3
       grind)
    | exact superpose eq1792 eq45437
    | exact resolve eq45437 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792 eq45437
  have eq67349 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq43494 y
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq43494
    | exact resolve eq43494 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq43494
  have eq67491 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq67349
       have i₂ := eq28849 (M.op y x) y
       grind)
    | exact superpose eq28849 eq67349
    | exact resolve eq67349 eq28849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67349
  have eq67529 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq67491
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq67491
    | exact resolve eq67491 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67491
  have eq67545 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq42720 eq67529
    | exact resolve eq67529 eq42720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42720 eq67529
  have eq96137 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6263 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq1759 X0 x X1
       grind)
    | exact superpose eq1759 eq6263
    | exact resolve eq6263 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq97023 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6263 eq96137
    | exact resolve eq96137 eq6263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96137
  have eq108690 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6239 eq6317
    | exact resolve eq6317 eq6239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239
  have eq108716 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X3)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6317 eq6263
    | exact resolve eq6263 eq6317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6317
  have eq108923 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6263 eq108716
    | exact resolve eq108716 eq6263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108716
  have eq112437 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6263 X2 (M.op X1 X0) (M.op (M.op x x) (M.op X1 X1)) X3
       have i₂ := eq7377 X0 x x X1
       grind)
    | exact superpose eq7377 eq6263
    | exact resolve eq6263 eq7377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7377
  have eq112473 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6263 eq112437
    | exact resolve eq112437 eq6263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6263 eq112437
  have eq162206 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq46002 eq108690
    | exact resolve eq108690 eq46002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46002 eq108690
  have eq162956 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq162206
       have i₂ := eq112473 sF2 sF2 (M.op sF4 sF4)
       grind)
    | exact superpose eq112473 eq162206
    | exact resolve eq162206 eq112473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162206
  have eq163292 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq245 eq162956
    | exact resolve eq162956 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq162956
  have eq163467 : (σ y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2826 eq163292
    | exact resolve eq163292 eq2826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826 eq163292
  have eq163836 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq163467
       have i₂ := eq112473 sF2 sF0 (M.op sF3 sF4)
       grind)
    | exact superpose eq112473 eq163467
    | exact resolve eq163467 eq112473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163467
  have eq240049 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq67545 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq67545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67545
  have eq240050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq240049
    | exact resolve eq240049 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240049
  have eq240061 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq240050
       have r₂ := eq28
       grind)
    | exact resolve eq240050 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240050
  have eq240082 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq240061 eq30073
    | exact resolve eq30073 eq240061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30073
  have eq240241 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq240061 eq254
    | exact resolve eq254 eq240061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq240314 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ y) (σ x)))) X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq240061 eq108923
    | exact resolve eq108923 eq240061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240323 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by grind
  have eq240331 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq108923 eq240314
    | exact resolve eq240314 eq108923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108923 eq240314
  have eq240370 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq240241
       have i₂ := eq97023 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq97023 eq240241
    | exact resolve eq240241 eq97023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240241
  have eq240468 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq240082
       have i₂ := eq97023 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq97023 eq240082
    | exact resolve eq240082 eq97023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97023 eq240082
  have eq240498 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq240370
       have i₂ := eq112473 sF2 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq112473 eq240370
    | exact resolve eq240370 eq112473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240370
  have eq240551 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq240468
       have i₂ := eq112473 sF2 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq112473 eq240468
    | exact resolve eq240468 eq112473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112473 eq240468
  have eq240557 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq163836 eq240498
    | exact resolve eq240498 eq163836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240498
  have eq240579 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq163836 eq240551
    | exact resolve eq240551 eq163836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163836 eq240551
  have eq241158 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq240061 eq240557
    | exact resolve eq240557 eq240061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240061 eq240557
  have eq241420 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq241158
  have eq241530 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq241420
       have r₂ := eq240323
       grind)
    | exact resolve eq241420 eq240323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240323 eq241420
  have eq242578 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq240331 eq241530
    | exact resolve eq241530 eq240331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240331 eq241530
  have eq243161 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq242578
  have eq244468 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq243161 eq51
    | exact resolve eq51 eq243161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq243161
  have eq262265 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq244468 eq240579
    | exact resolve eq240579 eq244468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240579 eq244468
  have eq262395 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq262265
  have eq262524 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq262395 eq142
    | exact resolve eq142 eq262395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq262395
  have eq262917 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq262524
    | exact resolve eq262524 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262524
  have eq262918 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq262917
  have eq263287 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28849 y y
       have i₂ := eq262918
       grind)
    | exact superpose eq262918 eq28849
    | exact resolve eq28849 eq262918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28849 eq262918
  have eq263323 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq263287
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq263287
    | exact resolve eq263287 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263287
  have eq263569 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq263323 eq30
    | exact resolve eq30 eq263323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq263323
  have eq263924 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq263569
    | exact resolve eq263569 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq263569
  have eq263925 : x = (M.op x y) ∨ x = y := by grind
  clear eq263924
  have eq263960 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq263925 eq21
    | exact resolve eq21 eq263925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264077 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq263925 eq2117
    | exact resolve eq2117 eq263925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117 eq263925
  have eq264433 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq264077
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq264077
    | exact resolve eq264077 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264077
  have eq264503 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq263960
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq263960
    | exact resolve eq263960 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263960
  have eq264551 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq264503 eq27
    | exact resolve eq27 eq264503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264503
  have eq266456 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2153 y
       have i₂ := eq264433
       grind)
    | exact superpose eq264433 eq2153
    | exact resolve eq2153 eq264433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq264433
  have eq266662 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq266456
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq266456
    | exact resolve eq266456 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266456
  have eq266760 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq266662
    | exact resolve eq266662 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266662
  have eq270103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq266760 eq264551
    | exact resolve eq264551 eq266760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264551 eq266760
  have eq270200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq270103
  have eq270244 : x = y := by
    first
    | (have r₁ := eq270200
       have r₂ := eq28
       grind)
    | exact resolve eq270200 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270200
  have eq270262 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq270244
       grind)
    | exact superpose eq270244 eq19
    | exact resolve eq19 eq270244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq270263 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq270244
       grind)
    | exact superpose eq270244 eq25
    | exact resolve eq25 eq270244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq270244
  have eq270790 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq270263
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq270263
    | exact resolve eq270263 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq270263
  have eq270867 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq270790 eq27
    | exact resolve eq27 eq270790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq270790
  have eq272077 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq270867 eq72
    | exact resolve eq72 eq270867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq270867
  have eq272507 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq272077
       have i₂ := eq270262
       grind)
    | exact superpose eq270262 eq272077
    | exact resolve eq272077 eq270262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270262 eq272077
  have eq275811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq272507 eq15
    | exact resolve eq15 eq272507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272507
  have eq276169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq275811
    | exact resolve eq275811 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq275811
  have eq276296 : False := by grind
  exact eq276296

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq134 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq56 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq134 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq134 X0 X1
       grind)
    | exact superpose eq134 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq134 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq134 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq134 X1 X1
       grind)
    | exact resolve eq13 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X2 X2))) = X2 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq134 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq134 X0 X1
       grind)
    | exact superpose eq134 eq9
    | (have j1 := eq134 X0 X1
       grind)
    | exact resolve eq9 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq188 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq191 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq188 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq188 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq209 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq65 X1 X1
       grind)
    | exact superpose eq65 eq137
    | exact resolve eq137 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq137
  have eq275 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq677 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X2) (M.op X1 (M.op X0 X1)))) ∨ (M.op X3 X2) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184 X2 X3 (M.op X0 X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq184
    | (have j0 := eq184 X2 X3 X2
       grind)
    | exact resolve eq184 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq184
  have eq10860 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X0 X0 X1
       have i₂ := eq209 X0 X0
       grind)
    | exact superpose eq209 eq677
    | (have j0 := eq677 X0 X1 X0 X1
       grind)
    | exact resolve eq677 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq677
  have eq10994 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq10860 X0 X1
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq10860 X0 X1
       have r₂ := eq275 X0 X1
       grind)
    | (have r₁ := eq10860 X0 X0
       have r₂ := eq275 X0 X0
       grind)
    | exact resolve eq10860 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq10860
  have eq11117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq10994 (σ X0) (σ X1)
       grind)
    | exact superpose eq10994 eq15
    | exact resolve eq15 eq10994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11127 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11117 X0 X1
       have i₂ := eq10994 X0 X1
       grind)
    | exact superpose eq10994 eq11117
    | exact resolve eq11117 eq10994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10994 eq11117
  have eq11247 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11127 y x
       grind)
    | exact superpose eq11127 eq16
    | (have r₁ := eq16
       have r₂ := eq11127 y x
       grind)
    | exact resolve eq16 eq11127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11127
  have eq11287 : False := by grind
  exact eq11287

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq266 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2
       have i₂ := eq136 X2 X0 X1
       grind)
    | exact superpose eq136 eq67
    | exact resolve eq67 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq325 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq266 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq266
    | exact resolve eq266 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq346 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq325 X0
       grind)
    | exact superpose eq325 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq689 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq346 X0
       have j1 := eq367 X0
       grind)
    | (have r₁ := eq346 X0
       have r₂ := eq367 X0
       grind)
    | exact resolve eq346 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq367
  have eq705 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq759 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq705 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq705
    | (have j0 := eq705 (σ X0) (σ X1)
       grind)
    | exact resolve eq705 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq759 y x
       grind)
    | exact superpose eq759 eq16
    | (have j1 := eq759 y x
       grind)
    | exact resolve eq16 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq1377 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 (M.op X1 X0) X2 X3
       have i₂ := eq136 X0 X0 X1
       grind)
    | exact superpose eq136 eq70
    | exact resolve eq70 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1450 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1377 X0 X1 x x
       have i₂ := eq70 X0 X0 x x
       grind)
    | exact superpose eq70 eq1377
    | exact resolve eq1377 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1377
  have eq2691 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq809
       have i₂ := eq705 y x
       grind)
    | exact superpose eq705 eq809
    | (have j1 := eq705 (σ y) (σ x)
       grind)
    | exact resolve eq809 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2694 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq2691
  have eq2717 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq689 (σ y)
       have i₂ := eq2694
       grind)
    | exact superpose eq2694 eq689
    | exact resolve eq689 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq2756 : (σ x) = (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2717
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2717
    | exact resolve eq2717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717
  have eq2762 : (k y x) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq2756
       grind)
    | exact superpose eq2756 eq10
    | exact resolve eq10 eq2756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2756
  have eq2794 : x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2762
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2762
    | exact resolve eq2762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq2798 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq705 y x
       have i₂ := eq2794
       grind)
    | exact superpose eq2794 eq705
    | (have j0 := eq705 y x
       grind)
    | exact resolve eq705 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq2794
  have eq2799 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq2798
  have eq2851 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1450 y y
       have i₂ := eq2799
       grind)
    | exact superpose eq2799 eq1450
    | exact resolve eq1450 eq2799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799
  have eq2853 : x = (M.op x y) := by grind
  clear eq2851
  have eq2886 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1450 y x
       have i₂ := eq2853
       grind)
    | exact superpose eq2853 eq1450
    | exact resolve eq1450 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq2888 : x = (M.op y y) := by
    first
    | (have i₁ := eq2886
       have i₂ := eq2853
       grind)
    | exact superpose eq2853 eq2886
    | exact resolve eq2886 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2886
  have eq3024 : x = (k y x) := by
    first
    | (have i₁ := eq689 y
       have i₂ := eq2888
       grind)
    | exact superpose eq2888 eq689
    | exact resolve eq689 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq2888
  have eq3175 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq809
       have i₂ := eq3024
       grind)
    | exact superpose eq3024 eq809
    | exact resolve eq809 eq3024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq3024
  have eq3179 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3175
       have i₂ := eq2853
       grind)
    | exact superpose eq2853 eq3175
    | exact resolve eq3175 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175
  have eq3180 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3179
  have eq4198 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq325 (σ y)
       have i₂ := eq3180
       grind)
    | exact superpose eq3180 eq325
    | exact resolve eq325 eq3180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq3180
  have eq4252 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4198
       grind)
    | exact superpose eq4198 eq16
    | exact resolve eq16 eq4198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4198
  have eq4295 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4252
       have i₂ := eq2853
       grind)
    | exact superpose eq2853 eq4252
    | exact resolve eq4252 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2853 eq4252
  have eq4296 : False := by grind
  exact eq4296

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq322 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq337 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq322 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq338 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq337 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq344 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq338 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq338 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq338 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq353 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq354 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq388 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq354 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq354
    | exact resolve eq354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq354 x y
       grind)
    | exact superpose eq354 eq16
    | exact resolve eq16 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq510 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq388 X0 (τ X1)
       grind)
    | exact superpose eq388 eq17
    | exact resolve eq17 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq388
  have eq526 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq510
    | exact resolve eq510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq533 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq526
    | exact resolve eq526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq633 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq400
       have i₂ := eq533 x y
       grind)
    | exact superpose eq533 eq400
    | exact resolve eq400 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq533
  have eq634 : False := by grind
  exact eq634

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq73
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq73 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq115 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X2 X0) (M.op X0 X0))
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq155 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq373 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq378 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq204 eq368
    | exact resolve eq368 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq726
    | exact resolve eq726 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq730 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq727
       have r₂ := eq27
       grind)
    | exact resolve eq727 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq733 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq730 eq53
    | exact resolve eq53 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq730 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq730
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq730
       grind)
    | exact resolve eq12 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq737 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq734
  have eq738 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq737
    | exact resolve eq737 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq739 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq733
    | exact resolve eq733 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq798 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X1)) X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq115 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1256 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq738 eq97
    | exact resolve eq97 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq1259 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1256
  have eq1262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1259 eq739
    | exact resolve eq739 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1259
  have eq1287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1262
  have eq1289 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1287
       have r₂ := eq27
       grind)
    | exact resolve eq1287 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1293 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq14
    | exact resolve eq14 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq53
    | exact resolve eq53 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1298 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1295
    | exact resolve eq1295 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1369 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq14
    | exact resolve eq14 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1376 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq207 X0 y
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq207
    | exact resolve eq207 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1382 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq426 y x
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq426
    | exact resolve eq426 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1426 : y = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq373 x y
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq373
    | exact resolve eq373 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq1468 : y = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1426
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1426
    | exact resolve eq1426 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1475 : y = (M.op y (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq204 eq1468
    | exact resolve eq1468 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1609 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1382 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1382 X0
       grind)
    | exact resolve eq13 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq1619 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1293 (M.op X0 (M.op X0 X0))
       have i₂ := eq395 X0 X0 X0
       grind)
    | exact superpose eq395 eq1293
    | exact resolve eq1293 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq1685 : y = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1475 eq1369
    | exact resolve eq1369 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1726 : y = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1685
  have eq1738 : y = (M.op (M.op x y) (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1726
       have i₂ := eq53 y sF0
       grind)
    | exact superpose eq53 eq1726
    | exact resolve eq1726 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1747 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1738 eq378
    | exact resolve eq378 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq1738
  have eq1764 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1747 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq12 (M.op x y) y
       have r₂ := eq1747
       grind)
    | exact resolve eq12 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq1775 : (M.op x y) = (M.op y (M.op x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1764
  have eq1777 : (M.op y (M.op x y)) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq204 eq1775
    | exact resolve eq1775 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775
  have eq1778 : (M.op y (M.op x y)) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq1777
       have r₂ := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq1777
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq1777 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1779 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1778 eq128
    | exact resolve eq128 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq2043 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1376 eq1369
    | exact resolve eq1369 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369 eq1376
  have eq2044 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2043 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2153 : (M.op y (M.op x y)) = (M.op x (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2044 eq1293
    | exact resolve eq1293 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq2044
  have eq2167 : (M.op y (M.op x y)) = (M.op x (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2153
  have eq2267 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2167
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq2167
    | exact resolve eq2167 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2285 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2267
  have eq2339 : (k (σ (M.op x y)) (σ y)) = (σ (M.op x (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2285 eq1779
    | exact resolve eq1779 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779 eq2285
  have eq2367 : (k (σ (M.op x y)) (σ y)) = (σ (M.op x (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2339
  have eq3439 : (M.op y x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x (M.op x x)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq372 x y
       have i₂ := eq1619 x
       grind)
    | exact superpose eq1619 eq372
    | exact resolve eq372 eq1619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq3466 : (M.op x x) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq372 eq3439
    | exact resolve eq3439 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq3439
  have eq3480 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1289
       have i₂ := eq3466
       grind)
    | exact superpose eq3466 eq1289
    | exact resolve eq1289 eq3466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289 eq3466
  have eq3492 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3480
  have eq3507 : x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq368 x
       have i₂ := eq3492
       grind)
    | exact superpose eq3492 eq368
    | exact resolve eq368 eq3492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq3492
  have eq3540 : x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3507
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3507
    | exact resolve eq3507 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq3602 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3540 eq2367
    | exact resolve eq2367 eq3540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367 eq3540
  have eq3639 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3602
  have eq3649 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3639
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3639
    | exact resolve eq3639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3639
  have eq3667 : (τ (σ x)) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3649 eq155
    | exact resolve eq155 eq3649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq3649
  have eq3669 : x = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq3667
    | exact resolve eq3667 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3667
  have eq3674 : x = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3669 eq1778
    | exact resolve eq1778 eq3669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778 eq3669
  have eq3677 : x = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3674
  have eq13454 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) (M.op X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq798 X0 X1
       have i₂ := eq426 X1 (M.op X0 X1)
       grind)
    | exact superpose eq426 eq798
    | (have j0 := eq798 X0 X1
       grind)
    | exact resolve eq798 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq798
  have eq13770 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13454 y y
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq13454
    | exact resolve eq13454 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298 eq13454
  have eq13914 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1609 (M.op x y)
       grind)
    | (have r₁ := eq13770
       have r₂ := eq1609 x
       grind)
    | exact resolve eq13770 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609 eq13770
  have eq14061 : (M.op x y) = (k y (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq204 eq13914
    | exact resolve eq13914 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq13914
  have eq14281 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3677 eq14061
    | exact resolve eq14061 eq3677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677 eq14061
  have eq14287 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14281
  have eq14294 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq14287
       grind)
    | exact superpose eq14287 eq73
    | exact resolve eq73 eq14287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq14287
  have eq14300 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14294
    | exact resolve eq14294 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14294
  have eq14309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14300 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq14300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq14312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14309
    | exact resolve eq14309 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14309
  have eq14315 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14312
       have r₂ := eq27
       grind)
    | exact resolve eq14312 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14312
  have eq14952 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14315 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14315
       grind)
    | exact resolve eq12 eq14315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14956 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14315 eq53
    | exact resolve eq53 eq14315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14315
  have eq14985 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14952
  have eq14993 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14956
    | exact resolve eq14956 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14956
  have eq14994 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14985
    | exact resolve eq14985 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14985
  have eq14995 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14994
  have eq15574 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14995 eq14300
    | exact resolve eq14300 eq14995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14300 eq14995
  have eq15579 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15574
  have eq15847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15579 eq14993
    | exact resolve eq14993 eq15579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14993 eq15579
  have eq15935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15847
  have eq15940 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15935
       have r₂ := eq27
       grind)
    | exact resolve eq15935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15935
  have eq15942 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq15940 eq27
    | exact resolve eq27 eq15940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq15944 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq15940 eq64
    | (have r₁ := eq64
       have r₂ := eq15940
       grind)
    | exact resolve eq64 eq15940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq15940
  have eq15984 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq15944
  have eq16396 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15984 eq97
    | exact resolve eq97 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq16397 : (τ (σ y)) = (k y x) := by
    first
    | exact superpose eq15984 eq80
    | exact resolve eq80 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq15984
  have eq16401 : y = (k y x) := by
    first
    | exact superpose eq29 eq16397
    | exact resolve eq16397 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16397
  have eq16402 : y = (M.op y x) := by
    first
    | (have r₁ := eq16396
       have r₂ := eq15942
       grind)
    | exact resolve eq16396 eq15942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16396
  have eq16424 : y ≠ y ∨ y = (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq16402
       grind)
    | exact superpose eq16402 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16402
       grind)
    | exact resolve eq12 eq16402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16428 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq16402
       grind)
    | exact superpose eq16402 eq53
    | exact resolve eq53 eq16402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq16402
  have eq16455 : y = (M.op x y) ∨ (k y x) = (M.op y y) := by grind
  clear eq16424
  have eq16464 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16428
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16428
    | exact resolve eq16428 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16428
  have eq16465 : y = (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq16455
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16455
    | exact resolve eq16455 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16455
  have eq16471 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16465
       have i₂ := eq16401
       grind)
    | exact superpose eq16401 eq16465
    | exact resolve eq16465 eq16401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16401 eq16465
  have eq19115 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16471
       have i₂ := eq16464
       grind)
    | exact superpose eq16464 eq16471
    | exact resolve eq16471 eq16464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16464 eq16471
  have eq19116 : y = (M.op x y) := by grind
  clear eq19115
  have eq19715 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq19116 eq20
    | exact resolve eq20 eq19116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19116
  have eq19887 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19715
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19715
    | exact resolve eq19715 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19715
  have eq19895 : False := by grind
  exact eq19895
