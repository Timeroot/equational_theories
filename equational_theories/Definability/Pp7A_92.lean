import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_y_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 (M.op X2 X3))) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op X2 (M.op X3 (M.op X2 X3)))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq9 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq70 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq35 X1 X2 (σ X0)
       grind)
    | exact superpose eq35 eq30
    | exact resolve eq30 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))
       have i₂ := eq72 (τ X0) X1 X2
       grind)
    | exact superpose eq72 eq17
    | exact resolve eq17 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq104 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X2 (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))
       have i₂ := eq73 (σ X0) X1 X2
       grind)
    | exact superpose eq73 eq30
    | exact resolve eq30 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq112 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (M.op X1 X2)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104
    | exact resolve eq104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq152 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))
       have i₂ := eq97 (τ X0) X1 X2
       grind)
    | exact superpose eq97 eq17
    | exact resolve eq17 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq157 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq152
    | exact resolve eq152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq178 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq77
    | (have j0 := eq77 X2 X2
       grind)
    | exact resolve eq77 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq196 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq196 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq213 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))
       have i₂ := eq157 (τ X0) X1 X2
       grind)
    | exact superpose eq157 eq17
    | exact resolve eq17 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq213 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213
    | exact resolve eq213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq451 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (k X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq35 X0 X1 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq35 eq198
    | (have j0 := eq198 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       grind)
    | exact resolve eq198 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq457 : ∀ X0 X1 X2 : G, (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1)))))) ≠ (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1)))))) ∨ (k X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) = (M.op X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X2
       have i₂ := eq112 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X0 X1
       grind)
    | exact superpose eq112 eq198
    | (have j0 := eq198 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X2
       grind)
    | exact resolve eq198 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq198
  have eq464 : ∀ X0 X1 X2 : G, (k X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) = (M.op X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq457 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq470 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq451 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq476 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) = (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq464 X0 X1 X2
       have i₂ := eq11 (τ (M.op X0 (M.op X1 (M.op X0 X1))))
       grind)
    | exact superpose eq11 eq464
    | exact resolve eq464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq482 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq470 X0 X1 X2
       have i₂ := eq72 X2 X0 X1
       grind)
    | exact superpose eq72 eq470
    | exact resolve eq470 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq470
  have eq487 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq476 X0 X1 X2
       have i₂ := eq73 X2 X0 X1
       grind)
    | exact superpose eq73 eq476
    | exact resolve eq476 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq476
  have eq621 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (τ (M.op X2 (M.op X3 (M.op X2 X3)))) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (τ (M.op X2 (M.op X3 (M.op X2 X3))))
       have i₂ := eq487 X2 X3 X0
       grind)
    | exact superpose eq487 eq9
    | exact resolve eq9 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq3004 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X3)) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq178 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) X3
       have i₂ := eq157 (τ X0) X1 X2
       grind)
    | exact superpose eq157 eq178
    | (have j0 := eq178 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) X3
       grind)
    | exact resolve eq178 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq178
  have eq3088 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X3)) = (M.op X0 (σ X3)) ∨ (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3004 X0 X1 X2 X3
       have i₂ := eq218 X0 X1 X2
       grind)
    | exact superpose eq218 eq3004
    | (have j0 := eq3004 X0 X1 X2 X3
       grind)
    | exact resolve eq3004 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004
  have eq3116 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3088 X0 X1 X2 X3
       have i₂ := eq17 X0 X3
       grind)
    | exact superpose eq17 eq3088
    | (have j0 := eq3088 X0 X1 X2 X3
       grind)
    | exact resolve eq3088 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3088
  have eq3137 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq3116 X0 X1 X2 X3
       have j1 := eq12 X0 (σ X3)
       grind)
    | (have r₁ := eq3116 X0 X1 X2 X3
       have r₂ := eq12 X0 (σ X3)
       grind)
    | exact resolve eq3116 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq3154 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq3137 X0 x x X3
       have i₂ := eq218 X0 x x
       grind)
    | exact superpose eq218 eq3137
    | (have j0 := eq3137 X0 x x X3
       grind)
    | exact resolve eq3137 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq3137
  have eq3175 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3154 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3154
    | exact resolve eq3154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3154 (σ X0) X1
       grind)
    | exact superpose eq3154 eq15
    | (have j1 := eq3154 (σ X0) X1
       grind)
    | exact resolve eq15 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq3291 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq3175 (τ X1) X0
       grind)
    | exact superpose eq3175 eq18
    | (have j1 := eq3175 (τ X1) X0
       grind)
    | exact resolve eq18 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3175
  have eq4736 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3291 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3291
    | exact resolve eq3291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291
  have eq4788 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4736 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4736
    | (have j0 := eq4736 X0 X1
       grind)
    | exact resolve eq4736 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4736
  have eq18764 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3211 x y
       grind)
    | exact superpose eq3211 eq16
    | (have j1 := eq3211 x y
       grind)
    | exact resolve eq16 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq20092 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18764
       have i₂ := eq4788 y x
       grind)
    | exact superpose eq4788 eq18764
    | (have j1 := eq4788 (σ y) (σ x)
       grind)
    | (have r₁ := eq18764
       have r₂ := eq4788 y x
       grind)
    | exact resolve eq18764 eq4788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4788 eq18764
  have eq20095 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20092
  have eq20600 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq20095
       grind)
    | exact superpose eq20095 eq9
    | exact resolve eq9 eq20095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20095
  have eq20678 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op y x))) = X1 ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq20600 X1
       grind)
    | exact superpose eq20600 eq9
    | (have j1 := eq20600 X1
       grind)
    | exact resolve eq9 eq20600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20600
  have eq363466 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (M.op (σ y) (σ x)))) = X2 ∨ (M.op X0 (M.op X1 (M.op y X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X0 y x
       have i₂ := eq20678 X2 y
       grind)
    | exact superpose eq20678 eq19
    | (have j1 := eq20678 X2 X1
       grind)
    | exact resolve eq19 eq20678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20678
  have eq395256 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (τ (σ y)) X1))) = X0 ∨ (M.op X2 (M.op X3 (M.op y X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq621 X1 X0 (σ y) (σ x)
       have i₂ := eq363466 X2 X3 (σ y)
       grind)
    | exact superpose eq363466 eq621
    | (have j1 := eq363466 X2 X3 X2
       grind)
    | exact resolve eq621 eq363466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq363466
  have eq396798 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op y X1))) = X0 ∨ (M.op X2 (M.op X3 (M.op y X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq395256 X0 X1 X2 X3
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq395256
    | (have j0 := eq395256 X0 X1 X0 X1
       grind)
    | exact resolve eq395256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395256
  have eq429971 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X1 (M.op y X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq396798 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396798
  have eq429972 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op y X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq429971 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429971
  have eq431263 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq429972 y x
       grind)
    | exact superpose eq429972 eq9
    | exact resolve eq9 eq429972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431297 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq482 y x X0
       have i₂ := eq429972 y x
       grind)
    | exact superpose eq429972 eq482
    | exact resolve eq482 eq429972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq429972
  have eq442390 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq431297 (σ x)
       grind)
    | exact superpose eq431297 eq16
    | exact resolve eq16 eq431297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431297
  have eq442798 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq442390
       have i₂ := eq431263 x
       grind)
    | exact superpose eq431263 eq442390
    | exact resolve eq442390 eq431263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431263 eq442390
  have eq442799 : False := by grind
  exact eq442799

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq59 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq14 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq14 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq577 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq93 X0 X0
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq93 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq93 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq584 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq586 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq588 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq586 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq586 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq586 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq1443 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq588 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq588
    | (have j0 := eq588 (τ X0) X1
       grind)
    | exact resolve eq588 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq1465 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1443 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1443
    | (have j0 := eq1443 X0 X1
       grind)
    | exact resolve eq1443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443
  have eq1475 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1465 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1465
    | (have j0 := eq1465 X0 X1
       grind)
    | exact resolve eq1465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq3981 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq584 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq584
    | (have j0 := eq584 (τ X0)
       grind)
    | exact resolve eq584 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq4005 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3981 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3981
    | (have j0 := eq3981 X0
       grind)
    | exact resolve eq3981 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3981
  have eq4016 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4005 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4005
    | (have j0 := eq4005 X0
       grind)
    | exact resolve eq4005 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005
  have eq13750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq13750
    | exact resolve eq13750 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13750
  have eq13762 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq13751
       have r₂ := eq27
       grind)
    | exact resolve eq13751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13751
  have eq13764 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq13762
    | exact resolve eq13762 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13762
  have eq13879 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq13764 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq13764
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq13764
       grind)
    | exact resolve eq13 eq13764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13764
  have eq13889 : ∀ X0 : G, y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq13879 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13879
  have eq13890 : ∀ X0 X1 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq13889 X1
       grind)
    | exact superpose eq13889 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq13889 X1
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq13889 X0
       grind)
    | exact resolve eq13 eq13889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13889
  have eq13900 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13890
  have eq14075 : ∀ X0 : G, (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq87
       have i₂ := eq13900 (k sF3 sF3) x
       grind)
    | exact superpose eq13900 eq87
    | (have j1 := eq13900 X0 x
       grind)
    | exact resolve eq87 eq13900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq13900
  have eq14139 : ∀ X0 : G, y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq14075
    | (have j0 := eq14075 y
       grind)
    | exact resolve eq14075 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14075
  have eq14175 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14139 X0
       have j1 := eq1475 y X0
       grind)
    | (have r₁ := eq14139 X0
       have r₂ := eq1475 y x
       grind)
    | (have r₁ := eq14139 y
       have r₂ := eq1475 y x
       grind)
    | exact resolve eq14139 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq14139
  have eq14213 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4016 y
       have i₂ := eq14175 y
       grind)
    | exact superpose eq14175 eq4016
    | (have j0 := eq4016 y
       grind)
    | (have r₁ := eq4016 y
       have r₂ := eq14175 y
       grind)
    | exact resolve eq4016 eq14175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016 eq14175
  have eq14241 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14213
  have eq14313 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq14241
       grind)
    | exact superpose eq14241 eq14
    | exact resolve eq14 eq14241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14241
  have eq20729 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq14313 y
       grind)
    | exact superpose eq14313 eq14
    | exact resolve eq14 eq14313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14313
  have eq21009 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20729 x
       grind)
    | exact superpose eq20729 eq18
    | (have j1 := eq20729 x
       grind)
    | exact resolve eq18 eq20729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20729
  have eq21012 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21009
  have eq21033 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21012 eq27
    | exact resolve eq27 eq21012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21034 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21012 eq60
    | exact resolve eq60 eq21012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq21012
  have eq21223 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f21223_12 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
      intro X0 X1 X2
      grind
    have f21223_13 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
      intro X0
      grind
    have f21223_21 : X0 ≠ (k X0 (σ y)) := by grind
    have f21223_22 : x ≠ (M.op x y) := by grind
    have f21223_23 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f21223_13 X0
         grind)
      | (have r₁ := f21223_13 X0
         have r₂ := f21223_22
         grind)
      | exact resolve f21223_13 f21223_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f21223_47 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f21223_12 (σ y) (σ x) X0
         have i₂ := f21223_23 (σ y)
         grind)
      | exact superpose f21223_23 f21223_12
      | exact resolve f21223_12 f21223_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f21223_73 : X0 ≠ X0 := by
      first
      | (have i₁ := f21223_21
         have i₂ := f21223_47 X0
         grind)
      | exact superpose f21223_47 f21223_21
      | (have r₁ := f21223_21
         have r₂ := f21223_47 X0
         grind)
      | exact resolve f21223_21 f21223_47
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f21223_78 : False := by grind
    exact f21223_78
  clear eq21034
  have eq21551 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21223 eq115
    | exact resolve eq115 eq21223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq21223
  have eq21604 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq21551
  have eq21641 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21604
       have r₂ := eq21033
       grind)
    | exact resolve eq21604 eq21033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21033 eq21604
  have eq21828 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq21641
       grind)
    | exact superpose eq21641 eq14
    | exact resolve eq14 eq21641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21641
  have eq35465 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq21828 y
       grind)
    | exact superpose eq21828 eq14
    | exact resolve eq14 eq21828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21828
  have eq35587 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35465 x
       grind)
    | exact superpose eq35465 eq18
    | (have j1 := eq35465 x
       grind)
    | exact resolve eq18 eq35465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35465
  have eq35596 : x = (M.op x y) := by grind
  clear eq35587
  have eq35623 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq35596 eq20
    | exact resolve eq20 eq35596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq35626 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | exact superpose eq35596 eq59
    | exact resolve eq59 eq35596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq35596
  have eq35760 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35623
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35623
    | exact resolve eq35623 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35623
  have eq35892 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq35760 eq26
    | exact resolve eq26 eq35760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq35760
  have eq36247 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 y x X0
       have i₂ := eq35626 y
       grind)
    | exact superpose eq35626 eq64
    | exact resolve eq64 eq35626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq35626
  have eq36453 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq584 y
       have i₂ := eq36247 y
       grind)
    | exact superpose eq36247 eq584
    | (have j0 := eq584 y
       grind)
    | exact resolve eq584 eq36247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq36247
  have eq36497 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq36453
  have eq36526 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36497
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36497
    | exact resolve eq36497 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq36497
  have eq37218 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq36526 eq14
    | exact resolve eq14 eq36526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37240 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq36526 eq37218
    | exact resolve eq37218 eq36526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37218
  have eq37251 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq36526 eq37240
    | exact resolve eq37240 eq36526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36526 eq37240
  have eq37818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37251 eq35892
    | exact resolve eq35892 eq37251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35892 eq37251
  have eq37835 : False := by grind
  exact eq37835

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq47 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq151 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq169 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 X0 X1 X2
       have i₂ := eq22 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq22 eq151
    | exact resolve eq151 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq177 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq169
    | exact resolve eq169 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq181 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq22 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq22 eq177
    | exact resolve eq177 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq184 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq181
    | exact resolve eq181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq322 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99 x y
       grind)
    | exact superpose eq99 eq16
    | (have j1 := eq99 (M.op y y) y
       grind)
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq3100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq322
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq322
    | (have j1 := eq14 (M.op y y) y
       grind)
    | (have r₁ := eq322
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq322
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq322 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq3101 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq3100
  have eq34210 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3101
       grind)
    | exact superpose eq3101 eq16
    | exact resolve eq16 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq34211 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq34210
       have r₂ := eq22 x
       grind)
    | exact resolve eq34210 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34210
  have eq34213 : y = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq34211
       grind)
    | exact superpose eq34211 eq10
    | exact resolve eq10 eq34211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34211
  have eq34274 : x = y ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq34213
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34213
    | exact resolve eq34213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34213
  have eq34276 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34274
       grind)
    | exact superpose eq34274 eq16
    | exact resolve eq16 eq34274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34274
  have eq34277 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq34276
       have r₂ := eq22 x
       grind)
    | exact resolve eq34276 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq34276
  have eq34444 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq34277
       grind)
    | exact superpose eq34277 eq10
    | exact resolve eq10 eq34277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34277
  have eq34507 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34444
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq34444
    | exact resolve eq34444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34444
  have eq34508 : y = (M.op y y) := by grind
  clear eq34507
  have eq34562 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq34508
       grind)
    | exact superpose eq34508 eq9
    | exact resolve eq9 eq34508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34569 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq184 y y X0
       have i₂ := eq34508
       grind)
    | exact superpose eq34508 eq184
    | exact resolve eq184 eq34508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq34659 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34569 X0
       have i₂ := eq34508
       grind)
    | exact superpose eq34508 eq34569
    | exact resolve eq34569 eq34508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34569
  have eq34666 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq34562 X0
       have i₂ := eq34508
       grind)
    | exact superpose eq34508 eq34562
    | exact resolve eq34562 eq34508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34562
  have eq34742 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq34659 X0
       have i₂ := eq34508
       grind)
    | exact superpose eq34508 eq34659
    | exact resolve eq34659 eq34508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34659
  have eq34749 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq34666 X0
       have i₂ := eq34508
       grind)
    | exact superpose eq34508 eq34666
    | exact resolve eq34666 eq34508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34508 eq34666
  have eq36727 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34742 (σ x)
       grind)
    | exact superpose eq34742 eq16
    | exact resolve eq16 eq34742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34742
  have eq36785 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq36727
       have i₂ := eq34749 x
       grind)
    | exact superpose eq34749 eq36727
    | exact resolve eq36727 eq34749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34749 eq36727
  have eq36786 : False := by grind
  exact eq36786

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyy_y_pxy_pxx_pxy_Equation4521 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq49
    | exact resolve eq49 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq111 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq115 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq73 sF3
       grind)
    | exact superpose eq73 eq111
    | exact resolve eq111 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq115
    | exact resolve eq115 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq136 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq154 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq151
       have i₂ := eq73 sF1
       grind)
    | exact superpose eq73 eq151
    | exact resolve eq151 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq156 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq154
       have i₂ := eq73 sF0
       grind)
    | exact superpose eq73 eq154
    | exact resolve eq154 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq192 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq84 (σ X0) sF2
       grind)
    | exact superpose eq84 eq39
    | (have j1 := eq84 X0 (σ x)
       grind)
    | exact resolve eq39 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq244 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq57 x x
       have i₂ := eq14 sF2 x x x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq244 eq247
    | exact resolve eq247 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq358 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq255 eq259
    | exact resolve eq259 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq445 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 X1 X2 x y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq927 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq445
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq445 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq104 eq84
    | (have j0 := eq84 x (σ y)
       grind)
    | exact resolve eq84 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq2191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq2190
    | exact resolve eq2190 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2194 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2191
       have r₂ := eq27
       grind)
    | exact resolve eq2191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq2196 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2194 eq136
    | exact resolve eq136 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq2194
  have eq2232 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq2196
    | exact resolve eq2196 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2196
  have eq2233 : y = (M.op y y) := by grind
  clear eq2232
  have eq2242 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq2233
       grind)
    | exact superpose eq2233 eq117
    | exact resolve eq117 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq2253 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq2233
       grind)
    | exact superpose eq2233 eq56
    | exact resolve eq56 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2257 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq445 X0 y y
       have i₂ := eq2233
       grind)
    | exact superpose eq2233 eq445
    | exact resolve eq445 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq2233
  have eq2269 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq244 eq2253
    | exact resolve eq2253 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq2253
  have eq2277 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2242
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2242
    | exact resolve eq2242 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2242
  have eq2278 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2269
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2269
    | exact resolve eq2269 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2269
  have eq2334 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2277 eq57
    | exact resolve eq57 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2277
  have eq2349 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq255 eq2334
    | exact resolve eq2334 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq2334
  have eq2359 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq26 eq2349
    | exact resolve eq2349 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2349
  have eq2371 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2278 eq356
    | exact resolve eq356 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2488 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2371 eq156
    | exact resolve eq156 eq2371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq2371
  have eq2523 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2488
    | exact resolve eq2488 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2622 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq2523 eq927
    | exact resolve eq927 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2633 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq2523 eq2622
    | exact resolve eq2622 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523 eq2622
  have eq3055 : (σ (M.op x y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq2633 eq2257
    | exact resolve eq2257 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq3056 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2359 eq2257
    | exact resolve eq2257 eq2359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq4854 : (σ (k (k x x) x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq192 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq192
    | exact resolve eq192 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq192
  have eq4920 : (σ (k (k x x) x)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4854
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq4854
    | exact resolve eq4854 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854
  have eq4942 : (σ (k (k x x) x)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq358 eq4920
    | exact resolve eq4920 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq4920
  have eq4954 : (M.op (σ x) (σ y)) = (σ (k (k x x) x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2359 eq4942
    | exact resolve eq4942 eq2359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2359 eq4942
  have eq4962 : (M.op (σ x) (σ y)) = (σ (k (M.op x x) x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4954
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq4954
    | exact resolve eq4954 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq4954
  have eq34435 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x x) x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4962
       have i₂ := eq84 (M.op x x) x
       grind)
    | exact superpose eq84 eq4962
    | (have j1 := eq84 x (σ x)
       grind)
    | exact resolve eq4962 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq4962
  have eq34502 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq34435
       have i₂ := eq356 x
       grind)
    | exact superpose eq356 eq34435
    | exact resolve eq34435 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq34435
  have eq34514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2278 eq34502
    | exact resolve eq34502 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34502
  have eq34520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq34514
    | exact resolve eq34514 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34514
  have eq34523 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq34520
       have r₂ := eq27
       grind)
    | exact resolve eq34520 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34520
  have eq34796 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq34523 eq78
    | exact resolve eq78 eq34523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq34523
  have eq34890 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq34796
    | exact resolve eq34796 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq34796
  have eq34891 : x = (M.op x x) := by grind
  clear eq34890
  have eq34952 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq927 x x
       have i₂ := eq34891
       grind)
    | exact superpose eq34891 eq927
    | exact resolve eq927 eq34891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq34993 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2278 eq34952
    | exact resolve eq34952 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278 eq34952
  have eq35027 : x = (M.op x y) := by
    first
    | (have i₁ := eq34993
       have i₂ := eq34891
       grind)
    | exact superpose eq34891 eq34993
    | exact resolve eq34993 eq34891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34891 eq34993
  have eq35057 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq35027 eq20
    | exact resolve eq20 eq35027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq35027
  have eq35165 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35057
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35057
    | exact resolve eq35057 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35057
  have eq36000 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq35165 eq3056
    | exact resolve eq3056 eq35165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056 eq35165
  have eq36038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3055 eq36000
    | exact resolve eq36000 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055 eq36000
  have eq36054 : False := by grind
  exact eq36054

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pyy_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq57 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X3) ∨ (k X3 (M.op X0 X3)) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X0 X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 (M.op X0 X3)
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op X0 (M.op X1 X2))
       have r₂ := eq14 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq37
  have eq83 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq86 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq44
    | exact resolve eq44 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq87 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq50
    | exact resolve eq50 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq88 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq87
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq87
    | exact resolve eq87 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq86
    | exact resolve eq86 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq142 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq83 sF1
       grind)
    | exact superpose eq83 eq139
    | exact resolve eq139 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq83 sF0
       grind)
    | exact superpose eq83 eq142
    | exact resolve eq142 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq165 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq239 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq250 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq58 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ x) (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq58 x x
       have i₂ := eq14 sF2 x x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq301 : (M.op (σ x) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq250 eq252
    | exact resolve eq252 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq355 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq250 eq254
    | exact resolve eq254 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq534 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 x y X1 X2
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59
    | (have j0 := eq59 X0 X1 X2 x y
       grind)
    | exact resolve eq59 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1268 : ∀ X0 X3 : G, (M.op X0 X3) ≠ (M.op X0 (M.op x y)) ∨ (k X3 (M.op X0 X3)) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq71 X0 x x X3
       have i₂ := eq534 X0 x x
       grind)
    | (have i₁ := eq71 X0 x y X3
       have i₂ := eq534 X0 x x
       grind)
    | exact superpose eq534 eq71
    | (have j0 := eq71 X0 x y X3
       grind)
    | (have r₁ := eq71 X0 x x (M.op x y)
       have r₂ := eq534 X0 x x
       grind)
    | (have r₁ := eq71 X0 x y (M.op x x)
       have r₂ := eq534 X0 x x
       grind)
    | exact resolve eq71 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1269 : ∀ X0 X3 : G, (M.op X0 X3) ≠ (M.op X0 (M.op x y)) ∨ (k X3 (M.op X0 X3)) = (M.op (M.op X0 X3) (M.op x y)) := by
    intro X0 X3
    first
    | (have i₁ := eq1268 X0 X3
       have i₂ := eq534 (M.op X0 X3) X0 X3
       grind)
    | (have i₁ := eq1268 x y
       have i₂ := eq534 (M.op x y) x x
       grind)
    | exact superpose eq534 eq1268
    | (have j0 := eq1268 X0 X3
       grind)
    | (have r₁ := eq1268 X0 (M.op x x)
       have r₂ := eq534 X0 x x
       grind)
    | (have r₁ := eq1268 X0 (M.op x y)
       have r₂ := eq534 X0 x y
       grind)
    | exact resolve eq1268 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq1268
  have eq1351 : (M.op (σ x) (M.op x y)) ≠ (M.op (σ x) (M.op x y)) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op x y))) = (M.op (M.op (σ x) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq301 eq1269
    | (have j0 := eq1269 (σ x) (M.op x y)
       grind)
    | (have r₁ := eq1269 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq301
       grind)
    | exact resolve eq1269 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq1269
  have eq1364 : (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op x y))) = (M.op (M.op (σ x) (M.op x y)) (M.op x y)) := by grind
  clear eq1351
  have eq1378 : (M.op (σ x) (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq355 eq1364
    | exact resolve eq1364 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1523 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq2715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2715
    | exact resolve eq2715 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2715
  have eq2719 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2716
       have r₂ := eq28
       grind)
    | exact resolve eq2716 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq2721 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2719
    | exact resolve eq2719 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2719
  have eq2723 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2721 eq28
    | exact resolve eq28 eq2721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2724 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2721 eq73
    | (have r₁ := eq73
       have r₂ := eq2721
       grind)
    | exact resolve eq73 eq2721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2725 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2721 eq250
    | exact resolve eq250 eq2721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq2739 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2724
  have eq2741 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2725
    | exact resolve eq2725 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2746 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2741 eq355
    | exact resolve eq355 eq2741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq2741
  have eq2789 : (σ x) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2721 eq2746
    | exact resolve eq2746 eq2721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746
  have eq2820 : (σ x) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2789
  have eq2945 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2820 eq1378
    | exact resolve eq1378 eq2820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378 eq2820
  have eq2992 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2721 eq2945
    | exact resolve eq2945 eq2721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721 eq2945
  have eq2997 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2992
  have eq2998 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2997
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq2997
    | exact resolve eq2997 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq2997
  have eq3214 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2739 eq112
    | exact resolve eq112 eq2739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq3215 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2739 eq96
    | exact resolve eq96 eq2739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2739
  have eq3218 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq3214
  have eq3222 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq88 eq3215
    | exact resolve eq3215 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3215
  have eq3225 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq3222
       have r₂ := eq72
       grind)
    | exact resolve eq3222 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq3222
  have eq3255 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3218 eq2998
    | exact resolve eq2998 eq3218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2998 eq3218
  have eq3279 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3255
  have eq3293 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq3279
       have r₂ := eq2723
       grind)
    | exact resolve eq3279 eq2723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723 eq3279
  have eq3298 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3293 eq30
    | exact resolve eq30 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293
  have eq3319 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3298
    | exact resolve eq3298 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298
  have eq3320 : x = (M.op x y) ∨ x = y := by grind
  clear eq3319
  have eq3324 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3320 eq21
    | exact resolve eq21 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3331 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq3320 eq239
    | exact resolve eq239 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq3365 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3331
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3331
    | exact resolve eq3331 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3331
  have eq3371 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq3324
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3324
    | exact resolve eq3324 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3440 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq3365
       grind)
    | exact superpose eq3365 eq89
    | exact resolve eq89 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3468 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq3440
    | exact resolve eq3440 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3440
  have eq3502 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3371 eq3468
    | exact resolve eq3468 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq3536 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq3502
  have eq3552 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3536 eq165
    | exact resolve eq165 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq3536
  have eq3585 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq3552
    | exact resolve eq3552 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3552
  have eq3589 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3320 eq3585
    | exact resolve eq3585 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320 eq3585
  have eq3620 : x = (M.op x x) ∨ x = y := by grind
  clear eq3589
  have eq3642 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq3620
       grind)
    | exact superpose eq3620 eq89
    | exact resolve eq89 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq3676 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3642
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3642
    | exact resolve eq3642 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3642
  have eq11108 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1523 x y
       have i₂ := eq3225
       grind)
    | exact superpose eq3225 eq1523
    | (have j0 := eq1523 x y
       grind)
    | exact resolve eq1523 eq3225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523 eq3225
  have eq11289 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11108
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq11108
    | exact resolve eq11108 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq11108
  have eq11361 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11289
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11289
    | exact resolve eq11289 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11289
  have eq11408 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11361
       have r₂ := eq3676
       grind)
    | exact resolve eq11361 eq3676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3676 eq11361
  have eq11450 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11408
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11408
    | exact resolve eq11408 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11408
  have eq11492 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11450
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11450
    | exact resolve eq11450 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11450
  have eq11493 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq11492
  have eq11508 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11493
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11493
    | exact resolve eq11493 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11493
  have eq11518 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11508
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11508
    | exact resolve eq11508 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11508
  have eq11521 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11518
    | exact resolve eq11518 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11518
  have eq11524 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11521 eq28
    | exact resolve eq28 eq11521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11521
  have eq11574 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11524
       have r₂ := eq3371
       grind)
    | exact resolve eq11524 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371 eq11524
  have eq11576 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11574 eq30
    | exact resolve eq30 eq11574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11574
  have eq11615 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11576
    | exact resolve eq11576 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11576
  have eq11616 : x = y := by grind
  clear eq11615
  have eq11619 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11616
       grind)
    | exact superpose eq11616 eq19
    | exact resolve eq19 eq11616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11620 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11616
       grind)
    | exact superpose eq11616 eq25
    | exact resolve eq25 eq11616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11616
  have eq11644 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11620
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11620
    | exact resolve eq11620 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11620
  have eq11769 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11644 eq27
    | exact resolve eq27 eq11644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11644
  have eq11860 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11769 eq88
    | exact resolve eq88 eq11769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq11769
  have eq11908 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11860
       have i₂ := eq11619
       grind)
    | exact superpose eq11619 eq11860
    | exact resolve eq11860 eq11619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11619 eq11860
  have eq12226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11908 eq15
    | exact resolve eq15 eq11908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11908
  have eq12267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12226
    | exact resolve eq12226 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12226
  have eq12275 : False := by grind
  exact eq12275

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxy_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 (k X0 X1) (M.op X0 X1)
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq182 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 X1 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X1 X2 x
       have i₂ := eq16 X0 X3 X4 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op x (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq182 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq182
    | exact resolve eq182 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq182 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 x y
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq644 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq644 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq644
    | exact resolve eq644 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq684 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq693
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq693
    | exact resolve eq693 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq710 : (M.op x y) = (k y x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq684
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq684
    | exact resolve eq684 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1255 : ∀ X0 X1 X2 X3 : G, (M.op X1 (k X0 X0)) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184 X1 X2 X3 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq184
    | exact resolve eq184 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1272 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184 X0 X1 X2 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq184
    | (have j0 := eq184 X0 X1 X2 x y
       grind)
    | exact resolve eq184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq184
    | (have j0 := eq184 X0 X1 X2 (σ x) (σ y)
       grind)
    | exact resolve eq184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1364 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1255 X0 X1 x x
       have i₂ := eq1281 X1 x x
       grind)
    | (have i₁ := eq1255 X0 X0 (σ x) (σ y)
       have i₂ := eq1281 X0 X1 x
       grind)
    | exact superpose eq1281 eq1255
    | (have j0 := eq1255 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq1255 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq1281
  have eq1427 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq1272
    | (have j0 := eq1272 X0 (σ x) (σ y)
       grind)
    | exact resolve eq1272 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op x y)) := by
    intro X0 X3
    first
    | (have i₁ := eq16 X0 x x X3
       have i₂ := eq1272 X0 x x
       grind)
    | (have i₁ := eq16 X0 x y X3
       have i₂ := eq1272 X0 x x
       grind)
    | exact superpose eq1272 eq16
    | (have j0 := eq16 X0 x y X3
       grind)
    | exact resolve eq16 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1725 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1364 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1364
    | exact resolve eq1364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1786 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq1427 eq1725
    | exact resolve eq1725 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427 eq1725
  have eq1888 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1446 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq1446
    | exact resolve eq1446 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq2081 : ∀ X0 : G, (M.op (σ X0) (M.op x y)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1888 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1888
    | exact resolve eq1888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2465 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq645 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq645
    | exact resolve eq645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2481 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1888 X0
       have i₂ := eq645 X0
       grind)
    | exact superpose eq645 eq1888
    | exact resolve eq1888 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq1888
  have eq2539 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2465 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq2465
    | exact resolve eq2465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465
  have eq2562 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2539 X0
       have i₂ := eq2481 X0
       grind)
    | exact superpose eq2481 eq2539
    | exact resolve eq2539 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq2539
  have eq2580 : ∀ X0 : G, (M.op (σ X0) (M.op x y)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2562 X0
       have i₂ := eq2081 X0
       grind)
    | exact superpose eq2081 eq2562
    | exact resolve eq2562 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081 eq2562
  have eq2617 : (σ (M.op (M.op x y) y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq193 eq2580
    | exact resolve eq2580 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq2580
  have eq2636 : (M.op (σ x) (M.op x y)) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq2617
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2617
    | exact resolve eq2617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617
  have eq2777 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq710
       grind)
    | exact superpose eq710 eq40
    | exact resolve eq40 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq2778 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2777
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2777
    | exact resolve eq2777 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq2780 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq2778
    | exact resolve eq2778 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq21629 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq2780 eq701
    | exact resolve eq701 eq2780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq2780
  have eq21638 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq21629
       have r₂ := eq27
       grind)
    | exact resolve eq21629 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21629
  have eq21650 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq21638 eq98
    | exact resolve eq98 eq21638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq21638
  have eq21713 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq32 eq21650
    | exact resolve eq21650 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21650
  have eq21714 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21713
  have eq21738 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq191 x
       have i₂ := eq21714
       grind)
    | exact superpose eq21714 eq191
    | exact resolve eq191 eq21714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq21760 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1786 x X0
       have i₂ := eq21714
       grind)
    | exact superpose eq21714 eq1786
    | exact resolve eq1786 eq21714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786 eq21714
  have eq21787 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq21760 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21760
    | (have j0 := eq21760 X0
       grind)
    | exact resolve eq21760 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21760
  have eq21801 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21738
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21738
    | exact resolve eq21738 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21738
  have eq21911 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21801 eq2636
    | exact resolve eq2636 eq21801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2636 eq21801
  have eq21961 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq21911
    | exact resolve eq21911 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21911
  have eq29412 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21787 eq26
    | (have j1 := eq21787 (σ x)
       grind)
    | exact resolve eq26 eq21787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21787
  have eq29425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21961 eq29412
    | exact resolve eq29412 eq21961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21961 eq29412
  have eq29503 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq29425
       have r₂ := eq27
       grind)
    | exact resolve eq29425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29425
  have eq29557 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq29503 eq32
    | exact resolve eq32 eq29503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq29503
  have eq29608 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq29557
    | exact resolve eq29557 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29557
  have eq29609 : x = y := by grind
  clear eq29608
  have eq29613 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq29609
       grind)
    | exact superpose eq29609 eq18
    | exact resolve eq18 eq29609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq29614 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq29609
       grind)
    | exact superpose eq29609 eq24
    | exact resolve eq24 eq29609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq29609
  have eq29652 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29614
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29614
    | exact resolve eq29614 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29614
  have eq29653 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq29613
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq29613
    | exact resolve eq29613 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29613
  have eq29664 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29652 eq26
    | exact resolve eq26 eq29652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq29652
  have eq29712 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq29664
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq29664
    | exact resolve eq29664 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq29664
  have eq29725 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq29653
       grind)
    | exact superpose eq29653 eq40
    | exact resolve eq40 eq29653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq29653
  have eq29785 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq29725
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29725
    | exact resolve eq29725 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29725
  have eq29801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29712 eq29785
    | exact resolve eq29785 eq29712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29712 eq29785
  have eq29809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq29801
    | exact resolve eq29801 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq29801
  have eq29814 : False := by grind
  exact eq29814

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation4521 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq59 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq88 : x ≠ (M.op x y) ∨ x = y ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq37
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq94
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq16
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
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
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq124
  have eq128 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq127
  have eq167 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq220 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq59 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59
    | (have j0 := eq59 x y
       grind)
    | exact resolve eq59 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq235 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq60 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60
    | (have j0 := eq60 x y
       grind)
    | exact resolve eq60 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq499 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 x y X1 X2
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 X0 X1 X2 x y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq615 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq499
    | (have j0 := eq499 X0 (σ x) (σ y)
       grind)
    | exact resolve eq499 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq1274 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq75 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2491
    | exact resolve eq2491 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq2495 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2492
       have r₂ := eq28
       grind)
    | exact resolve eq2492 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492
  have eq2497 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2495
    | exact resolve eq2495 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495
  have eq2500 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2497 eq89
    | (have r₁ := eq89
       have r₂ := eq2497
       grind)
    | exact resolve eq89 eq2497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq2501 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2497 eq235
    | exact resolve eq235 eq2497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq2504 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2497 eq615
    | exact resolve eq615 eq2497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq2497
  have eq2510 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2500
  have eq2511 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2510
  have eq2513 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2501
    | exact resolve eq2501 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501
  have eq2758 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2511 eq109
    | exact resolve eq109 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq2759 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2511 eq106
    | exact resolve eq106 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq2511
  have eq2762 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2758
  have eq2766 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq74 eq2759
    | exact resolve eq2759 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq2769 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2766
       have r₂ := eq88
       grind)
    | exact resolve eq2766 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq2766
  have eq2801 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2762 eq2504
    | exact resolve eq2504 eq2762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504 eq2762
  have eq2819 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2801
  have eq2958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2819 eq2513
    | exact resolve eq2513 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513 eq2819
  have eq2981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2958
  have eq2995 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2981
       have r₂ := eq28
       grind)
    | exact resolve eq2981 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq3001 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2995 eq30
    | exact resolve eq30 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq3022 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3001
    | exact resolve eq3001 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq3023 : x = (M.op x y) ∨ x = y := by grind
  clear eq3022
  have eq3028 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3023 eq21
    | exact resolve eq21 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3035 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq3023 eq220
    | exact resolve eq220 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq3060 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3035
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3035
    | exact resolve eq3035 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3066 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq3028
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3028
    | exact resolve eq3028 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028
  have eq3120 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq3060
       grind)
    | exact superpose eq3060 eq52
    | exact resolve eq52 eq3060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060
  have eq3143 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq3120
    | exact resolve eq3120 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3176 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3066 eq3143
    | exact resolve eq3143 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143
  have eq3204 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq3176
  have eq3215 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3204 eq167
    | exact resolve eq167 eq3204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq3204
  have eq3242 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq3215
    | exact resolve eq3215 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3215
  have eq3245 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3023 eq3242
    | exact resolve eq3242 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023 eq3242
  have eq3268 : x = (M.op x x) ∨ x = y := by grind
  clear eq3245
  have eq3280 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq3268
       grind)
    | exact superpose eq3268 eq52
    | exact resolve eq52 eq3268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3312 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3280
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3280
    | exact resolve eq3280 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq10950 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1274 x y
       have i₂ := eq2769
       grind)
    | exact superpose eq2769 eq1274
    | (have j0 := eq1274 x y
       grind)
    | exact resolve eq1274 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274 eq2769
  have eq11050 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10950
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq10950
    | exact resolve eq10950 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq10950
  have eq11103 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11050
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11050
    | exact resolve eq11050 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11050
  have eq11149 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11103
       have r₂ := eq3312
       grind)
    | exact resolve eq11103 eq3312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3312 eq11103
  have eq11188 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11149
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11149
    | exact resolve eq11149 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11149
  have eq11226 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11188
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11188
    | exact resolve eq11188 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11188
  have eq11246 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11226
    | exact resolve eq11226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11226
  have eq11259 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11246
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11246
    | exact resolve eq11246 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11246
  have eq11262 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11259
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11259
    | exact resolve eq11259 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11259
  have eq11263 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11262
  have eq11266 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11263 eq28
    | exact resolve eq28 eq11263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11263
  have eq11308 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11266
       have r₂ := eq3066
       grind)
    | exact resolve eq11266 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066 eq11266
  have eq11310 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11308 eq30
    | exact resolve eq30 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11308
  have eq11351 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11310
    | exact resolve eq11310 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11310
  have eq11352 : x = y := by grind
  clear eq11351
  have eq11355 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11352
       grind)
    | exact superpose eq11352 eq19
    | exact resolve eq19 eq11352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11356 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11352
       grind)
    | exact superpose eq11352 eq25
    | exact resolve eq25 eq11352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11352
  have eq11380 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11356
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11356
    | exact resolve eq11356 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11356
  have eq11514 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11380 eq27
    | exact resolve eq27 eq11380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11380
  have eq11602 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11514 eq74
    | exact resolve eq74 eq11514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq11514
  have eq11645 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11602
       have i₂ := eq11355
       grind)
    | exact superpose eq11355 eq11602
    | exact resolve eq11602 eq11355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11355 eq11602
  have eq11650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11645 eq15
    | exact resolve eq15 eq11645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11645
  have eq11693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11650
    | exact resolve eq11650 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq11650
  have eq11701 : False := by grind
  exact eq11701

/-- `Equation4538`: `x ◇ (y ◇ z) = (y ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyy_y_pyx_Equation4538 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4538 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4538.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq52 : ∀ X0 X1 : G, (M.op (M.op x X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y X1
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) X1 (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X1) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq52 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq52 X2 x
       have i₂ := eq52 X0 x
       grind)
    | (have i₁ := eq52 X0 (M.op x y)
       have i₂ := eq52 (M.op x (M.op x y)) x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op x X2) X3)) = (M.op (M.op X0 (M.op x y)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op x X2) X3 X2
       have i₂ := eq52 X0 X2
       grind)
    | (have i₁ := eq9 X0 X0 X2 (M.op x y)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X3) X3) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op x (M.op X1 x)) X1 x X3
       have i₂ := eq52 X0 (M.op X1 x)
       grind)
    | (have i₁ := eq9 X0 x y X3
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op (M.op x X0) X0) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op x X1) X2 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq100 : ∀ X1 X2 X3 : G, (M.op (M.op x y) y) = (M.op X1 (M.op X2 X3)) := by
    intro X1 X2 X3
    first
    | exact superpose eq84 eq97
    | exact resolve eq97 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq102 : ∀ X0 X2 : G, (M.op (M.op x y) y) = (M.op (M.op X0 (M.op x y)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq94 X0 x X2 x
       have i₂ := eq100 x (M.op x X2) x
       grind)
    | exact superpose eq100 eq94
    | exact resolve eq94 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq103 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq62 x x
       have i₂ := eq100 x sF2 x
       grind)
    | exact superpose eq100 eq62
    | exact resolve eq62 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq164 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | (have i₁ := eq63 X0 (M.op (σ x) (σ y))
       have i₂ := eq63 (M.op sF2 (M.op (σ x) (σ y))) x
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (σ x) X2) X3)) = (M.op (M.op X0 (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X0 X2 (M.op (σ x) (σ y))
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq63 eq84
    | exact resolve eq84 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq186 : ∀ X0 X2 : G, (M.op (M.op x y) y) = (M.op (M.op X0 (M.op (σ x) (σ y))) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq175 X0 x X2 x
       have i₂ := eq100 x (M.op sF2 X2) x
       grind)
    | exact superpose eq100 eq175
    | exact resolve eq175 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq192 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X0 X3) ∨ (k (M.op X0 X3) X2) = (M.op X2 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X0 X3) X2
       have i₂ := eq9 X2 X0 X3 X1
       grind)
    | (have i₁ := eq12 X3 (M.op X1 X3)
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X3) X2
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 X2)) (M.op X1 (M.op X0 (M.op X1 X2)))
       have r₂ := eq9 X0 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66 eq218
    | exact resolve eq218 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq430 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (M.op X1 sF0)
       have i₂ := eq96 X0 X1 sF0
       grind)
    | exact superpose eq96 eq84
    | exact resolve eq84 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq441 : ∀ X0 X2 X3 : G, (M.op X0 X3) ≠ (M.op (M.op x y) y) ∨ (k (M.op X0 X3) X2) = (M.op X2 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq192 X0 x X2 X3
       have i₂ := eq430 X0 x
       grind)
    | (have i₁ := eq192 x y X2 X3
       have i₂ := eq430 X0 x
       grind)
    | exact superpose eq430 eq192
    | (have j0 := eq192 X0 x X2 X3
       grind)
    | (have r₁ := eq192 (M.op x y) x X2 y
       have r₂ := eq430 (M.op x y) x
       grind)
    | exact resolve eq192 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq512 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | exact superpose eq102 eq102
    | exact resolve eq102 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) ∨ (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x y) y) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq512 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq512 eq12
    | (have j0 := eq12 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq12 (M.op (M.op x y) y) (M.op (M.op x y) y)
       have r₂ := eq512 (M.op (M.op x y) y)
       grind)
    | exact resolve eq12 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 : G, (M.op (M.op x y) y) = (k X0 (M.op (M.op x y) y)) ∨ (M.op (M.op x y) y) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq774 X0
       have i₂ := eq100 (M.op sF0 y) sF0 y
       grind)
    | exact superpose eq100 eq774
    | (have j0 := eq774 X0
       grind)
    | (have r₁ := eq774 (M.op x (M.op x x))
       have r₂ := eq100 x x x
       grind)
    | exact resolve eq774 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq790 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x y) y) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq773 X0
       grind)
    | (have r₁ := eq773 X0
       have r₂ := eq100 (M.op (M.op x y) y) (M.op x y) y
       grind)
    | exact resolve eq773 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq795 : ∀ X0 : G, (M.op (M.op x y) y) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq790 (k X0 (M.op (M.op x y) y))
       have j1 := eq789 X0
       grind)
    | (have r₁ := eq790 X0
       have r₂ := eq789 X0
       grind)
    | (have r₁ := eq790 (M.op (M.op x y) y)
       have r₂ := eq789 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq790 X0
       have r₂ := eq789 (k X0 (M.op (M.op x y) y))
       grind)
    | exact resolve eq790 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq790
  have eq797 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X1 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq181 eq795
    | exact resolve eq795 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (k X1 (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq84 eq795
    | exact resolve eq795 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq837 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq841 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq837
    | exact resolve eq837 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq845 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq841
    | exact resolve eq841 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq847 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq845
    | exact resolve eq845 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq854 : ∀ X0 X1 : G, (k (σ (σ X0)) X1) = (σ (σ (k X0 (τ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (σ X0)
       have i₂ := eq48 (τ X1) X0
       grind)
    | exact superpose eq48 eq48
    | exact resolve eq48 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) (τ X2))) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X2 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq48
    | exact resolve eq48 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq866 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq795 eq49
    | exact resolve eq49 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq864 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq864
    | exact resolve eq864 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : ∀ X0 X1 : G, (τ (M.op X0 (M.op (σ x) (σ y)))) = (k X1 (τ (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq797 eq864
    | exact resolve eq864 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 : G, (τ (M.op X0 (M.op x y))) = (k X1 (τ (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq799 eq864
    | exact resolve eq864 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq864
  have eq1836 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op X3 X3) = (k (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq100 eq441
    | (have j0 := eq441 X0 X3 (M.op X1 X2)
       grind)
    | (have r₁ := eq441 X1 X2 (M.op X2 X3)
       have r₂ := eq100 X1 X2 X3
       grind)
    | exact resolve eq441 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1837 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) ≠ (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op X1 X1) = (k (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq181 eq441
    | (have j0 := eq441 X0 X1 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq441 X0 x (M.op (σ x) (σ y))
       have r₂ := eq181 X0
       grind)
    | exact resolve eq441 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1839 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op X0 (M.op x y)) ∨ (M.op X1 X1) = (k (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq84 eq441
    | (have j0 := eq441 X0 X1 (M.op x y)
       grind)
    | (have r₁ := eq441 X0 x (M.op x y)
       have r₂ := eq84 X0
       grind)
    | exact resolve eq441 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq441 (M.op x y) X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq1848 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1850 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1837 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq1851 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (k (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1836 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1877 : ∀ X0 : G, (k (τ (M.op (M.op x y) y)) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1846 eq936
    | exact resolve eq936 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1882 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1846 eq902
    | exact resolve eq902 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1928 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X1 (M.op x y))) (τ X0)) := by
    intro X0 X1
    first
    | exact superpose eq1848 eq936
    | exact resolve eq936 eq1848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq1967 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X1 (M.op (σ x) (σ y)))) (τ X0)) := by
    intro X0 X1
    first
    | exact superpose eq1850 eq936
    | exact resolve eq936 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2146 : (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq181 eq1877
    | exact resolve eq1877 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2150 : ∀ X0 : G, (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) (τ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq102 eq1877
    | exact resolve eq1877 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq2151 : ∀ X0 : G, (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) (τ (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq186 eq1877
    | exact resolve eq1877 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq2168 : ∀ X0 : G, (τ (M.op (M.op x y) y)) = (τ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq946 eq2151
    | exact resolve eq2151 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq2169 : ∀ X0 : G, (τ (M.op (M.op x y) y)) = (τ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq947 eq2150
    | exact resolve eq2150 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2194 : ∀ X0 X1 : G, (τ (M.op X1 (M.op (σ x) (σ y)))) = (τ (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq84 eq2168
    | exact resolve eq2168 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2195 : ∀ X0 X1 : G, (τ (M.op X0 (M.op (σ x) (σ y)))) = (τ (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2168 eq2168
    | exact resolve eq2168 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3134 : ∀ X0 X1 : G, (τ (M.op X1 (M.op (σ x) (σ y)))) = (k (τ (M.op X0 (M.op x y))) (τ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2194 sF0 X1
       have i₂ := eq1928 sF0 X1
       grind)
    | exact superpose eq1928 eq2194
    | exact resolve eq2194 eq1928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928 eq2194
  have eq3317 : ∀ X0 X1 : G, (τ (M.op X1 (M.op (σ x) (σ y)))) = (k (τ (M.op X0 (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2195 X0 sF4
       have i₂ := eq1967 sF4 X1
       grind)
    | exact superpose eq1967 eq2195
    | exact resolve eq2195 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3589 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (σ (k X0 (τ (τ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq854 X0 (σ X1)
       grind)
    | exact superpose eq854 eq15
    | exact resolve eq15 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq3620 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (σ (k X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3589 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3589
    | exact resolve eq3589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq4014 : ∀ X0 X1 : G, (σ (σ (k X1 (τ (M.op X0 (M.op x y)))))) = (σ (k (σ X1) (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq2169 eq3620
    | exact resolve eq3620 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq4015 : ∀ X0 X1 : G, (σ (σ (k X1 (τ (M.op X0 (M.op (σ x) (σ y))))))) = (σ (k (σ X1) (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq2168 eq3620
    | exact resolve eq3620 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq4103 : ∀ X0 X1 : G, (σ (M.op (M.op x y) y)) = (σ (σ (k X1 (τ (M.op X0 (M.op (σ x) (σ y))))))) := by
    intro X0 X1
    first
    | exact superpose eq795 eq4015
    | exact resolve eq4015 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4015
  have eq4104 : ∀ X0 X1 : G, (σ (M.op (M.op x y) y)) = (σ (σ (k X1 (τ (M.op X0 (M.op x y)))))) := by
    intro X0 X1
    first
    | exact superpose eq795 eq4014
    | exact resolve eq4014 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014
  have eq4135 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (σ (σ (τ (M.op X0 (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq946 eq4103
    | exact resolve eq4103 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4103
  have eq4136 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (σ (σ (τ (M.op X0 (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq947 eq4104
    | exact resolve eq4104 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947 eq4104
  have eq4156 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (σ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq4135 X0
       have i₂ := eq11 (M.op X0 sF4)
       grind)
    | exact superpose eq11 eq4135
    | exact resolve eq4135 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq4157 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4136 X0
       have i₂ := eq11 (M.op X0 sF0)
       grind)
    | exact superpose eq11 eq4136
    | exact resolve eq4136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq12401 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X2 (k X0 (τ X1))
       have i₂ := eq856 X0 X1 X2
       grind)
    | exact superpose eq856 eq48
    | exact resolve eq48 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16134 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (k (σ (τ X0)) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 (k X1 (τ X2))
       have i₂ := eq866 X1 X2 (τ X0)
       grind)
    | exact superpose eq866 eq49
    | exact resolve eq49 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq16206 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (k X0 (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16134 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16134
    | exact resolve eq16134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16134
  have eq20617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq847
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq847
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq847 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20617
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20617
    | exact resolve eq20617 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20617
  have eq20638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20635
    | exact resolve eq20635 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20635
  have eq20639 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20638
       have r₂ := eq27
       grind)
    | exact resolve eq20638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20638
  have eq20640 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20639
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20639
    | exact resolve eq20639 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20639
  have eq20641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20640
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20640
    | exact resolve eq20640 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20640
  have eq20642 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20641 eq225
    | (have r₁ := eq225
       have r₂ := eq20641
       grind)
    | exact resolve eq225 eq20641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq20641
  have eq20678 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20642
  have eq20679 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20678
  have eq20684 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20679
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq20679
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq20679 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20689 : (τ (σ x)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq20679
       grind)
    | exact superpose eq20679 eq10
    | exact resolve eq10 eq20679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20679
  have eq20712 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq20689
    | exact resolve eq20689 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20689
  have eq20715 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20684
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20684
    | exact resolve eq20684 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20684
  have eq20716 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20712
       have r₂ := eq217
       grind)
    | exact resolve eq20712 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq20712
  have eq20719 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20715
    | exact resolve eq20715 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20715
  have eq20722 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20719
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20719
    | exact resolve eq20719 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20719
  have eq20723 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20722
  have eq20726 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20723
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20723
    | exact resolve eq20723 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20723
  have eq20727 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20726
  have eq20734 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq847
       have i₂ := eq20716
       grind)
    | exact superpose eq20716 eq847
    | exact resolve eq847 eq20716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20736 : (τ x) = (k (τ y) (τ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq936 y x
       have i₂ := eq20716
       grind)
    | exact superpose eq20716 eq936
    | exact resolve eq936 eq20716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20716
  have eq20738 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20734
  have eq20742 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20738
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20738
    | exact resolve eq20738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20738
  have eq20763 : ∀ X0 : G, (τ (M.op x y)) = (k (τ (M.op X0 (M.op (σ x) (σ y)))) (τ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1967 x X0
       have i₂ := eq20727
       grind)
    | exact superpose eq20727 eq1967
    | exact resolve eq1967 eq20727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq20776 : (M.op (M.op x y) y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq430 x x
       have i₂ := eq20727
       grind)
    | exact superpose eq20727 eq430
    | exact resolve eq430 eq20727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq20727
  have eq20800 : ∀ X0 : G, (σ (k X0 (τ x))) = (k (σ X0) (k y (σ (τ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq909 y (τ x) X0
       have i₂ := eq20736
       grind)
    | exact superpose eq20736 eq909
    | exact resolve eq909 eq20736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq20804 : (τ (τ x)) = (k (τ (τ y)) (τ (τ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq936 (τ y) (τ x)
       have i₂ := eq20736
       grind)
    | exact superpose eq20736 eq936
    | exact resolve eq936 eq20736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20736
  have eq20809 : ∀ X0 : G, (σ (k X0 (τ x))) = (k (σ X0) (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20800 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq20800
    | exact resolve eq20800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20800
  have eq21069 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20776 eq84
    | exact resolve eq84 eq20776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21079 : ∀ X0 : G, (σ (M.op (M.op x y) x)) = (k X0 (σ (M.op (M.op x y) x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20776 eq902
    | exact resolve eq902 eq20776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21090 : ∀ X0 : G, (τ (M.op X0 (M.op (σ x) (σ y)))) = (τ (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20776 eq2168
    | exact resolve eq2168 eq20776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq21104 : ∀ X0 : G, (σ (M.op X0 (M.op (σ x) (σ y)))) = (σ (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20776 eq4156
    | exact resolve eq4156 eq20776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156 eq20776
  have eq21405 : ∀ X0 : G, (τ (M.op X0 (M.op (σ x) (σ y)))) = (k (τ (M.op (M.op x y) x)) (τ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21069 eq3134
    | exact resolve eq3134 eq21069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3134 eq21069
  have eq22420 : ∀ X0 : G, (k (k (σ (τ (τ y))) (τ x)) X0) = (σ (k (τ (τ x)) (τ X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq856 (τ (τ y)) (τ x) X0
       have i₂ := eq20804
       grind)
    | exact superpose eq20804 eq856
    | exact resolve eq856 eq20804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq20804
  have eq22431 : ∀ X0 : G, (k (k (σ (τ (τ y))) (τ x)) X0) = (k (τ x) (σ (τ X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22420 X0
       have i₂ := eq49 (τ x) (τ X0)
       grind)
    | exact superpose eq49 eq22420
    | exact resolve eq22420 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22420
  have eq22434 : ∀ X0 : G, (k (τ x) X0) = (k (k (σ (τ (τ y))) (τ x)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22431 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22431
    | exact resolve eq22431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22431
  have eq22436 : ∀ X0 : G, (k (τ x) X0) = (k (σ (k (τ (τ y)) (τ (τ x)))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22434 X0
       have i₂ := eq12401 (τ (τ y)) (τ x) X0
       grind)
    | exact superpose eq12401 eq22434
    | exact resolve eq22434 eq12401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12401 eq22434
  have eq22438 : ∀ X0 : G, (k (τ x) X0) = (k (k (τ y) (σ (τ (τ x)))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22436 X0
       have i₂ := eq49 (τ y) (τ (τ x))
       grind)
    | exact superpose eq49 eq22436
    | exact resolve eq22436 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22436
  have eq22440 : ∀ X0 : G, (k (k (τ y) (τ x)) X0) = (k (τ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22438 X0
       have i₂ := eq11 (τ x)
       grind)
    | exact superpose eq11 eq22438
    | exact resolve eq22438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22438
  have eq23868 : ∀ X0 : G, (k X0 (σ (τ x))) = (k (σ (τ X0)) (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49 X0 (τ x)
       have i₂ := eq20809 (τ X0)
       grind)
    | exact superpose eq20809 eq49
    | exact resolve eq49 eq20809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20809
  have eq23959 : ∀ X0 : G, (k X0 (σ (τ x))) = (k X0 (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23868 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23868
    | exact resolve eq23868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23868
  have eq24036 : ∀ X0 : G, (k X0 x) = (k X0 (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23959 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq23959
    | exact resolve eq23959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23959
  have eq24157 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 (σ (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49 X0 (k y x)
       have i₂ := eq24036 (τ X0)
       grind)
    | exact superpose eq24036 eq49
    | exact resolve eq49 eq24036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24036
  have eq24188 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24157 X0
       have i₂ := eq49 X0 x
       grind)
    | exact superpose eq49 eq24157
    | exact resolve eq24157 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24157
  have eq24219 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24188 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24188
    | (have j0 := eq24188 X0
       grind)
    | exact resolve eq24188 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24188
  have eq24421 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24219 X0
       have i₂ := eq847
       grind)
    | exact superpose eq847 eq24219
    | exact resolve eq24219 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24219
  have eq24528 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq24421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24421
  have eq27461 : ∀ X0 X1 : G, (σ (k X1 (τ (M.op X0 (M.op (σ x) (σ y)))))) = (k (σ X1) (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21090 eq48
    | exact resolve eq48 eq21090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21090
  have eq27502 : ∀ X0 X1 : G, (σ (τ (M.op X0 (M.op (σ x) (σ y))))) = (k (σ X1) (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq946 eq27461
    | exact resolve eq27461 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27461
  have eq27539 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k (σ X1) (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq27502 X0 X1
       have i₂ := eq11 (M.op X0 sF4)
       grind)
    | exact superpose eq11 eq27502
    | exact resolve eq27502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27502
  have eq27831 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op X0 (M.op (σ x) (σ y))))) = (σ (k (M.op x y) (M.op (M.op x y) x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21104 eq28
    | exact resolve eq28 eq21104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21104
  have eq27861 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 (M.op (σ x) (σ y))))) = (σ (k (M.op x y) (M.op (M.op x y) x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28 eq27831
    | exact resolve eq27831 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq27831
  have eq27900 : ∀ X0 : G, (σ (M.op X0 (M.op (σ x) (σ y)))) = (σ (k (M.op x y) (M.op (M.op x y) x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq797 eq27861
    | exact resolve eq27861 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27861
  have eq35597 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (τ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq24528 eq48
    | exact resolve eq48 eq24528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq35632 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op X0 (M.op X1 X2)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq24528 eq1851
    | exact resolve eq1851 eq24528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24528
  have eq35659 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35632 x x x
       have i₂ := eq1851 x x x sF2
       grind)
    | exact superpose eq1851 eq35632
    | exact resolve eq35632 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35632
  have eq35683 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (τ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq30 eq35597
    | exact resolve eq35597 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35597
  have eq35720 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq181 eq35659
    | exact resolve eq35659 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35659
  have eq41421 : (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq35720
  have eq41438 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq100 eq41421
    | exact resolve eq41421 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41421
  have eq53129 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (k X0 (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq27539 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27539
    | exact resolve eq27539 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53304 : ∀ X0 : G, (τ (M.op x y)) = (k (τ (k (σ X0) (M.op (M.op x y) x))) (τ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27539 eq20763
    | exact resolve eq20763 eq27539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20763 eq27539
  have eq53425 : ∀ X0 : G, (τ (M.op x y)) = (k (τ (k (σ X0) (M.op (M.op x y) x))) (τ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq53304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53304
  have eq53533 : ∀ X0 : G, (τ (M.op x y)) = (k (k (τ (σ X0)) (τ (M.op (M.op x y) x))) (τ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53425 X0
       have i₂ := eq936 (σ X0) (M.op sF0 x)
       grind)
    | exact superpose eq936 eq53425
    | exact resolve eq53425 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq53425
  have eq53579 : ∀ X0 : G, (τ (M.op x y)) = (k (k X0 (τ (M.op (M.op x y) x))) (τ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53533 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53533
    | exact resolve eq53533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53533
  have eq53623 : ∀ X0 X2 : G, (k X0 (M.op (M.op x y) x)) = (k X2 (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X2
    first
    | exact superpose eq53129 eq53129
    | exact resolve eq53129 eq53129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53943 : ∀ X0 X2 : G, (k X0 (M.op (M.op x y) x)) = (k X2 (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X2
    first
    | (have j0 := eq53623 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53623
  have eq84537 : ∀ X0 X1 : G, (k X1 (k (σ (k (τ y) (τ x))) X0)) = (k X1 (σ (k (τ x) (τ X0)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16206 X1 (k (τ y) (τ x)) X0
       have i₂ := eq22440 (τ X0)
       grind)
    | exact superpose eq22440 eq16206
    | exact resolve eq16206 eq22440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16206 eq22440
  have eq85340 : ∀ X0 X1 : G, (k X1 (k (σ (k (τ y) (τ x))) X0)) = (k X1 (k x (σ (τ X0)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq84537 X0 X1
       have i₂ := eq49 x (τ X0)
       grind)
    | exact superpose eq49 eq84537
    | exact resolve eq84537 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84537
  have eq85531 : ∀ X0 X1 : G, (k X1 (k x X0)) = (k X1 (k (σ (k (τ y) (τ x))) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq85340 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85340
    | exact resolve eq85340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85340
  have eq85624 : ∀ X0 X1 : G, (k X1 (k x X0)) = (k X1 (k (k y (σ (τ x))) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq85531 X0 X1
       have i₂ := eq49 y (τ x)
       grind)
    | exact superpose eq49 eq85531
    | exact resolve eq85531 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85531
  have eq85681 : ∀ X0 X1 : G, (k X1 (k x X0)) = (k X1 (k (k y x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq85624 X0 X1
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq85624
    | exact resolve eq85624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85624
  have eq86856 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op (σ x) (σ y)))) = (k X1 (k x (M.op (M.op x y) x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq53129 eq85681
    | exact resolve eq85681 eq53129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53129 eq85681
  have eq87172 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op (σ x) (σ y)))) = (k X1 (k x (M.op (M.op x y) x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq86856 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86856
  have eq87233 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X1 (k x (M.op (M.op x y) x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq797 eq87172
    | exact resolve eq87172 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq87172
  have eq119564 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21079 eq1851
    | exact resolve eq1851 eq21079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21079
  have eq147796 : ∀ X0 : G, (k (σ (M.op X0 (M.op (σ x) (σ y)))) (σ (M.op x y))) = (σ (k (k (M.op x y) (M.op (M.op x y) x)) (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27900 eq29
    | exact resolve eq29 eq27900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27900
  have eq147910 : ∀ X0 : G, (σ (k (M.op X0 (M.op (σ x) (σ y))) (M.op x y))) = (σ (k (k (M.op x y) (M.op (M.op x y) x)) (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq147796
    | exact resolve eq147796 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147796
  have eq147994 : (σ (M.op (M.op x y) (M.op x y))) = (σ (k (k (M.op x y) (M.op (M.op x y) x)) (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1850 eq147910
    | exact resolve eq147910 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147910
  have eq148055 : (σ (M.op (M.op x y) y)) = (σ (k (k (M.op x y) (M.op (M.op x y) x)) (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4157 eq147994
    | exact resolve eq147994 eq4157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157 eq147994
  have eq215581 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (k X2 (k X0 (M.op (M.op x y) x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq53943 eq87233
    | exact resolve eq87233 eq53943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53943 eq87233
  have eq216053 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (k X2 (k X0 (M.op (M.op x y) x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq215581 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215581
  have eq255447 : ∀ X0 X1 X3 : G, (M.op (M.op x y) y) = (M.op (k X0 (k X1 (M.op (M.op x y) x))) X3) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1 X3
    first
    | exact superpose eq216053 eq186
    | exact resolve eq186 eq216053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216053
  have eq306561 : ∀ X0 : G, (σ (τ (M.op X0 (M.op (σ x) (σ y))))) = (k (M.op (M.op x y) x) (σ (τ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21405 eq49
    | exact resolve eq49 eq21405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21405
  have eq306572 : ∀ X0 : G, (σ (τ (M.op X0 (M.op (σ x) (σ y))))) = (k (M.op (M.op x y) x) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq306561 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq306561
    | exact resolve eq306561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306561
  have eq306581 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (k (M.op (M.op x y) x) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq306572 X0
       have i₂ := eq11 (M.op X0 sF4)
       grind)
    | exact superpose eq11 eq306572
    | exact resolve eq306572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306572
  have eq306617 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (k (M.op (M.op x y) x) (M.op x y)) X1) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq306581 eq186
    | exact resolve eq186 eq306581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq306581
  have eq343579 : ∀ X0 : G, (σ (τ (M.op x y))) = (k (k X0 (σ (τ (M.op (M.op x y) x)))) (σ (τ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53579 eq908
    | exact resolve eq908 eq53579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53579
  have eq343582 : ∀ X0 : G, (σ (τ (M.op x y))) = (k (k X0 (σ (τ (M.op (M.op x y) x)))) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq343579 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq343579
    | exact resolve eq343579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343579
  have eq343604 : ∀ X0 : G, (σ (τ (M.op x y))) = (k (k X0 (M.op (M.op x y) x)) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq343582 X0
       have i₂ := eq11 (M.op sF0 x)
       grind)
    | exact superpose eq11 eq343582
    | exact resolve eq343582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343582
  have eq343615 : ∀ X0 : G, (M.op x y) = (k (k X0 (M.op (M.op x y) x)) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq343604 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq343604
    | exact resolve eq343604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343604
  have eq343762 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op (M.op x y) x))) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq343615 eq908
    | exact resolve eq908 eq343615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq343615
  have eq343840 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op (M.op x y) x))) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq343762 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq343762
    | (have j0 := eq343762 X0
       grind)
    | exact resolve eq343762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343762
  have eq343903 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op (M.op x y) x))) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq343840
    | (have j0 := eq343840 X0
       grind)
    | exact resolve eq343840 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343840
  have eq344415 : (σ (M.op x y)) = (k (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq343903 (M.op x (M.op x x))
       have i₂ := eq1851 x x x (σ (M.op sF0 x))
       grind)
    | exact superpose eq1851 eq343903
    | exact resolve eq343903 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343903
  have eq390255 : ∀ X0 X1 : G, (σ (τ (M.op X0 (M.op (σ x) (σ y))))) = (σ (k (τ (M.op X1 (M.op (σ x) (σ y)))) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq3317 eq35683
    | exact resolve eq35683 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317 eq35683
  have eq390309 : ∀ X0 X1 : G, (σ (τ (M.op X0 (M.op (σ x) (σ y))))) = (k (M.op X1 (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq390255 X0 X1
       have i₂ := eq49 (M.op X1 sF4) x
       grind)
    | exact superpose eq49 eq390255
    | exact resolve eq390255 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390255
  have eq390324 : ∀ X0 : G, (σ (τ (M.op X0 (M.op (σ x) (σ y))))) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1850 eq390309
    | exact resolve eq390309 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850 eq390309
  have eq390336 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (τ (M.op X0 (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq390324 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq390324
    | (have j0 := eq390324 X0
       grind)
    | exact resolve eq390324 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390324
  have eq390345 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq390336 X0
       have i₂ := eq11 (M.op X0 sF4)
       grind)
    | exact superpose eq11 eq390336
    | exact resolve eq390336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390336
  have eq490470 : (τ (σ (M.op (M.op x y) y))) = (k (k (M.op x y) (M.op (M.op x y) x)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq148055 eq10
    | exact resolve eq10 eq148055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148055
  have eq490471 : (M.op (M.op x y) y) = (k (k (M.op x y) (M.op (M.op x y) x)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq490470
       have i₂ := eq10 (M.op sF0 y)
       grind)
    | exact superpose eq10 eq490470
    | exact resolve eq490470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490470
  have eq743266 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ (M.op (M.op x y) x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq119564 eq100
    | exact resolve eq100 eq119564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119564
  have eq743335 : (σ (M.op x y)) = (k (M.op (M.op x y) y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq743266 eq344415
    | exact resolve eq344415 eq743266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344415 eq743266
  have eq743348 : (σ (M.op x y)) = (k (M.op (M.op x y) y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq743335
  have eq743355 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1846 eq743348
    | exact resolve eq743348 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq743348
  have eq743368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq743355 eq20742
    | exact resolve eq20742 eq743355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20742
  have eq743383 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq743355 eq390345
    | exact resolve eq390345 eq743355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390345
  have eq743435 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq743355 eq41438
    | exact resolve eq41438 eq743355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41438 eq743355
  have eq743446 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq743435 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743435
  have eq743454 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq743383 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743383
  have eq743469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq743368
  have eq743480 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq743446 X0
       grind)
    | (have r₁ := eq743446 X0
       have r₂ := eq27
       grind)
    | exact resolve eq743446 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743446
  have eq743486 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq743454 X0
       grind)
    | (have r₁ := eq743454 X0
       have r₂ := eq27
       grind)
    | exact resolve eq743454 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743454
  have eq743492 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq743469
       have r₂ := eq27
       grind)
    | exact resolve eq743469 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743469
  have eq743500 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq743492 eq164
    | exact resolve eq164 eq743492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743556 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  have eq743633 : (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq255447 eq743480
    | exact resolve eq743480 eq255447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255447 eq743480
  have eq743639 : (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq743633
  have eq746371 : ∀ X1 : G, (τ (σ (M.op x y))) = (k X1 (τ (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X1
    first
    | exact superpose eq743486 eq946
    | exact resolve eq946 eq743486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743486
  have eq746794 : ∀ X1 : G, (M.op x y) = (k X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X1
    first
    | exact superpose eq37 eq746371
    | exact resolve eq746371 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746371
  have eq748333 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq746794 eq306617
    | exact resolve eq306617 eq746794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306617
  have eq748673 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq746794 eq490471
    | exact resolve eq490471 eq746794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490471 eq746794
  have eq750023 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq748673
  have eq750320 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq748333 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748333
  have eq753279 : (M.op x y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq750023 eq743639
    | exact resolve eq743639 eq750023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750023
  have eq753337 : (M.op x y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq753279
  have eq761535 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq743500 eq26
    | (have j1 := eq743500 (σ x) X0
       grind)
    | exact resolve eq26 eq743500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743500
  have eq761732 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq761535 eq103
    | exact resolve eq103 eq761535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761535
  have eq761867 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1 X2
    first
    | exact superpose eq761732 eq100
    | exact resolve eq100 eq761732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761876 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq761732 eq512
    | exact resolve eq512 eq761732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761732
  have eq762377 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq743492 eq761876
    | exact resolve eq761876 eq743492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743492 eq761876
  have eq763319 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq762377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762377
  have eq763328 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq763319 X0
       grind)
    | (have r₁ := eq763319 X0
       have r₂ := eq743556
       grind)
    | exact resolve eq763319 eq743556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763319
  have eq765539 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq763328 eq946
    | exact resolve eq946 eq763328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763328
  have eq765987 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39 eq765539
    | exact resolve eq765539 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765539
  have eq769817 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1851 x x x y
       have i₂ := eq765987 (M.op x (M.op x x))
       grind)
    | exact superpose eq765987 eq1851
    | exact resolve eq1851 eq765987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765987
  have eq819971 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq750320 eq743639
    | exact resolve eq743639 eq750320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743639 eq750320
  have eq820280 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq819971 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819971
  have eq848027 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq761867 X0 y y
       have i₂ := eq769817
       grind)
    | exact superpose eq769817 eq761867
    | exact resolve eq761867 eq769817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761867
  have eq848514 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq848027 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848027
  have eq848767 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq848514 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq848514 x
       grind)
    | exact superpose eq848514 eq18
    | (have j1 := eq848514 x
       grind)
    | exact resolve eq18 eq848514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848781 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq769817
       have i₂ := eq848514 y
       grind)
    | exact superpose eq848514 eq769817
    | exact resolve eq769817 eq848514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769817 eq848514
  have eq848906 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq848781
  have eq849060 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq848767 eq103
    | exact resolve eq103 eq848767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849224 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq849060
    | exact resolve eq849060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849060
  have eq849883 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq849224 eq820280
    | (have r₁ := eq820280 y
       have r₂ := eq849224
       grind)
    | exact resolve eq820280 eq849224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820280 eq849224
  have eq849927 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq849883
  have eq849928 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq849927
  have eq849982 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq849928
       have r₂ := eq753337
       grind)
    | exact resolve eq849928 eq753337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753337 eq849928
  have eq850017 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq848767 eq849982
    | exact resolve eq849982 eq848767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848767
  have eq850018 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq848906 eq849982
    | exact resolve eq849982 eq848906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848906
  have eq850023 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq849982 eq164
    | exact resolve eq164 eq849982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq850130 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq850018
  have eq850131 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq850017
  have eq850495 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq850131 eq850130
    | exact resolve eq850130 eq850131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850130 eq850131
  have eq850496 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq850495
  have eq850543 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq850496 eq39
    | exact resolve eq39 eq850496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850558 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq850496 eq743556
    | (have r₁ := eq743556
       have r₂ := eq850496
       grind)
    | exact resolve eq743556 eq850496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743556 eq850496
  have eq850609 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq850558
  have eq850610 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq850609
  have eq850619 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq850543
    | exact resolve eq850543 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850543
  have eq850866 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq850619 eq38
    | exact resolve eq38 eq850619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850619
  have eq850904 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq850866
    | exact resolve eq850866 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850866
  have eq853796 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq850023 eq26
    | (have j1 := eq850023 (σ x) X0
       grind)
    | exact resolve eq26 eq850023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850023
  have eq854446 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq853796 eq103
    | exact resolve eq103 eq853796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq853796
  have eq854681 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq854446 eq512
    | exact resolve eq512 eq854446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq854446
  have eq855998 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq849982 eq854681
    | exact resolve eq854681 eq849982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849982
  have eq856001 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq850610 eq854681
    | exact resolve eq854681 eq850610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850610
  have eq857538 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq856001 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856001
  have eq857541 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq855998 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855998
  have eq861474 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq857538 eq946
    | exact resolve eq946 eq857538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq861486 : ∀ X0 : G, (τ (σ x)) = (τ (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq857538 eq2195
    | exact resolve eq2195 eq857538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195 eq857538
  have eq862272 : ∀ X0 : G, x = (τ (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq38 eq861486
    | exact resolve eq861486 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861486
  have eq862280 : ∀ X0 : G, x = (k X0 x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq38 eq861474
    | exact resolve eq861474 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861474
  have eq863133 : (σ y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq857541 eq181
    | exact resolve eq181 eq857541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857541
  have eq876187 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1851 x x x x
       have i₂ := eq862280 (M.op x (M.op x x))
       grind)
    | exact superpose eq862280 eq1851
    | exact resolve eq1851 eq862280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862280
  have eq880292 : (τ (σ y)) = (k (τ (σ y)) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq863133 eq2146
    | exact resolve eq2146 eq863133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146 eq863133
  have eq880514 : y = (k y (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39 eq880292
    | exact resolve eq880292 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq880292
  have eq884070 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq854681 eq862272
    | exact resolve eq862272 eq854681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854681 eq862272
  have eq884226 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq884070
  have eq892493 : y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq884226 eq880514
    | exact resolve eq880514 eq884226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880514 eq884226
  have eq892606 : y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq892493
  have eq893258 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq892606
       grind)
    | exact superpose eq892606 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq892606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892606
  have eq893260 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq893258
  have eq893730 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq893260
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq893260
    | exact resolve eq893260 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893260
  have eq893731 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq893730
  have eq893736 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq893731
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq893731
    | exact resolve eq893731 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893731
  have eq893810 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq876187
       have i₂ := eq893736
       grind)
    | exact superpose eq893736 eq876187
    | exact resolve eq876187 eq893736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876187 eq893736
  have eq893885 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq893810
  have eq893966 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq893885 eq38
    | exact resolve eq38 eq893885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq893885
  have eq894006 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq893966
    | exact resolve eq893966 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq893966
  have eq894007 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq894006
  have eq894014 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq894007 eq87
    | exact resolve eq87 eq894007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq894162 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq894007
  have eq896081 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq894014 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq894014 X0 x
       grind)
    | exact superpose eq894014 eq18
    | (have j1 := eq894014 x X0
       grind)
    | exact resolve eq18 eq894014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894014
  have eq896780 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq896081 sF0
       grind)
    | exact superpose eq896081 eq84
    | exact resolve eq84 eq896081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq896781 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X1 X2 x
       have i₂ := eq896081 sF0
       grind)
    | exact superpose eq896081 eq100
    | exact resolve eq100 eq896081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896793 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq902 X0
       have i₂ := eq896081 sF0
       grind)
    | exact superpose eq896081 eq902
    | exact resolve eq902 eq896081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896081
  have eq897153 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq896793
    | (have j0 := eq896793 X0
       grind)
    | exact resolve eq896793 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896793
  have eq897158 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq850904 eq896780
    | exact resolve eq896780 eq850904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896780
  have eq898589 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq897158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897158
  have eq898606 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq898589 X0
       grind)
    | (have r₁ := eq898589 X0
       have r₂ := eq894162
       grind)
    | exact resolve eq898589 eq894162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898589
  have eq908715 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq897153 eq29
    | exact resolve eq29 eq897153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq897153
  have eq911328 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq902 X0
       have i₂ := eq898606 sF0
       grind)
    | exact superpose eq898606 eq902
    | exact resolve eq902 eq898606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq898606
  have eq911682 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq911328 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq911328
    | (have j0 := eq911328 X0
       grind)
    | exact resolve eq911328 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911328
  have eq919251 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq911682 eq1851
    | exact resolve eq1851 eq911682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911682
  have eq922507 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq850904 eq908715
    | exact resolve eq908715 eq850904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850904 eq908715
  have eq924203 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq922507 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922507
  have eq924278 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq924203 X0
       grind)
    | (have r₁ := eq924203 X0
       have r₂ := eq894162
       grind)
    | exact resolve eq924203 eq894162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894162 eq924203
  have eq927801 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49 X0 y
       have i₂ := eq924278 (τ X0)
       grind)
    | exact superpose eq924278 eq49
    | exact resolve eq49 eq924278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq924278
  have eq928348 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq927801 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq927801
    | (have j0 := eq927801 X0
       grind)
    | exact resolve eq927801 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq927801
  have eq931914 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq928348 eq1851
    | exact resolve eq1851 eq928348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851 eq928348
  have eq939194 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq919251 eq896781
    | exact resolve eq896781 eq919251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896781 eq919251
  have eq939874 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq939194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939194
  have eq940361 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq939874 eq26
    | (have j1 := eq939874 (σ x)
       grind)
    | exact resolve eq26 eq939874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940363 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq939874 eq931914
    | exact resolve eq931914 eq939874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931914 eq939874
  have eq940374 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq940363
  have eq940466 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq940361 eq27
    | exact resolve eq27 eq940361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940361
  have eq940732 : x = (M.op x y) := by
    first
    | (have r₁ := eq940466
       have r₂ := eq940374
       grind)
    | exact resolve eq940466 eq940374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940374 eq940466
  have eq940733 : x = (M.op x y) := by
    first
    | exact superpose eq940732 eq18
    | exact resolve eq18 eq940732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq940734 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq940732 eq20
    | exact resolve eq20 eq940732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq940746 : ∀ X1 X2 X3 : G, (M.op x y) = (M.op X1 (M.op X2 X3)) := by
    intro X1 X2 X3
    first
    | exact superpose eq940732 eq100
    | exact resolve eq100 eq940732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq940752 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq940732 eq181
    | exact resolve eq181 eq940732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq940800 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq940732 eq795
    | exact resolve eq795 eq940732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq940827 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq940732 eq1882
    | exact resolve eq1882 eq940732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882 eq940732
  have eq997804 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq940734
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq940734
    | exact resolve eq940734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940734
  have eq997806 : ∀ X1 X2 X3 : G, x = (M.op X1 (M.op X2 X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq940746 X1 X2 X3
       have i₂ := eq940733
       grind)
    | exact superpose eq940733 eq940746
    | exact resolve eq940746 eq940733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940746
  have eq997810 : ∀ X0 : G, x = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq940752 X0
       have i₂ := eq940733
       grind)
    | exact superpose eq940733 eq940752
    | exact resolve eq940752 eq940733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940752
  have eq997820 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq940800 X0
       have i₂ := eq940733
       grind)
    | exact superpose eq940733 eq940800
    | exact resolve eq940800 eq940733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940800
  have eq997828 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq940827
       have i₂ := eq940733
       grind)
    | exact superpose eq940733 eq940827
    | exact resolve eq940827 eq940733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940733 eq940827
  have eq1001353 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq997804 eq22
    | exact resolve eq22 eq997804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1001354 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq997804 eq26
    | exact resolve eq26 eq997804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1001365 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq997804 eq847
    | exact resolve eq847 eq997804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq997804
  have eq1019836 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1001365
       have i₂ := eq997820 y
       grind)
    | exact superpose eq997820 eq1001365
    | exact resolve eq1001365 eq997820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997820 eq1001365
  have eq1019848 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq997828
       have i₂ := eq1001353
       grind)
    | exact superpose eq1001353 eq997828
    | exact resolve eq997828 eq1001353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997828
  have eq1029172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1019836
       have i₂ := eq1001353
       grind)
    | exact superpose eq1001353 eq1019836
    | exact resolve eq1019836 eq1001353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001353 eq1019836
  have eq1036032 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1029172
       have r₂ := eq27
       grind)
    | exact resolve eq1029172 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029172
  have eq1040418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1019848 eq1036032
    | exact resolve eq1036032 eq1019848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036032
  have eq1042064 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1040418
       have r₂ := eq27
       grind)
    | exact resolve eq1040418 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040418
  have eq1042921 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1042064 eq27
    | exact resolve eq27 eq1042064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1042930 : ∀ X0 : G, x = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1042064 eq997810
    | exact resolve eq997810 eq1042064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997810
  have eq1042940 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1042064 eq1001354
    | exact resolve eq1001354 eq1042064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001354 eq1042064
  have eq1043473 : x = (σ y) := by
    first
    | exact superpose eq1042930 eq1042940
    | exact resolve eq1042940 eq1042930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042930 eq1042940
  have eq1044892 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1043473 eq1042921
    | exact resolve eq1042921 eq1043473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042921 eq1043473
  have eq1062866 : ∀ X0 : G, x = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1019848 eq997806
    | exact resolve eq997806 eq1019848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997806
  have eq1063016 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq1062866 eq1019848
    | exact resolve eq1019848 eq1062866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019848 eq1062866
  have eq1063144 : False := by grind
  exact eq1063144
