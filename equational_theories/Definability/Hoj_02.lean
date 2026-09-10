import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq76 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq77 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq66 (σ X0) (σ X0)
       grind)
    | exact superpose eq66 eq76
    | exact resolve eq76 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq66 (τ X0) (τ X0)
       grind)
    | exact superpose eq66 eq75
    | exact resolve eq75 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq90 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq64
    | exact resolve eq64 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq591 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq780 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 x
       have i₂ := eq591 x x
       grind)
    | exact superpose eq591 eq77
    | (have j1 := eq591 X0 X0
       grind)
    | exact resolve eq77 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq591
  have eq807 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq809 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq780 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq810 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq807 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq807
    | (have j0 := eq807 X0
       grind)
    | exact resolve eq807 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq813 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq809 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq809
    | (have j0 := eq809 X0
       grind)
    | exact resolve eq809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq873 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq813 (σ X0)
       grind)
    | exact superpose eq813 eq23
    | (have j1 := eq813 (σ X0)
       grind)
    | exact resolve eq23 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq881 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq873 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq873
    | (have j0 := eq873 X0
       grind)
    | exact resolve eq873 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq897 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq881 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq881
    | (have j0 := eq881 X0
       grind)
    | exact resolve eq881 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq4973 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq897 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq897
    | (have j0 := eq897 (τ X0)
       grind)
    | exact resolve eq897 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq5053 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq4973 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq4973
    | (have j0 := eq4973 X0
       grind)
    | exact resolve eq4973 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4973
  have eq5093 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5053 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5053
    | (have j0 := eq5053 X0
       grind)
    | exact resolve eq5053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5053
  have eq5187 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq5093 X0
       grind)
    | exact superpose eq5093 eq77
    | (have j1 := eq5093 X0
       grind)
    | exact resolve eq77 eq5093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq5194 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X0) X1
       have i₂ := eq5093 X0
       grind)
    | exact superpose eq5093 eq68
    | (have j1 := eq5093 X0
       grind)
    | exact resolve eq68 eq5093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq5243 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5194 X0 X1
       have i₂ := eq64 (σ X0) X1
       grind)
    | exact superpose eq64 eq5194
    | (have j0 := eq5194 X0 X1
       grind)
    | exact resolve eq5194 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194
  have eq5247 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5187 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5187
    | (have j0 := eq5187 X0
       grind)
    | exact resolve eq5187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5187
  have eq5298 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (τ (k (σ X0) (σ X0))) = (τ (k (k (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq5247 (σ X0)
       grind)
    | exact superpose eq5247 eq29
    | (have j1 := eq5247 (σ X0)
       grind)
    | exact resolve eq29 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5247
  have eq5354 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (k (σ X0) (σ X0))) = (τ (k (k (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5298 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5298
    | (have j0 := eq5298 X0
       grind)
    | exact resolve eq5298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5298
  have eq5409 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5354 X0
       have i₂ := eq23 (k (σ X0) (σ X0)) X0
       grind)
    | exact superpose eq23 eq5354
    | (have j0 := eq5354 X0
       grind)
    | exact resolve eq5354 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354
  have eq5461 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5409 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq5409
    | (have j0 := eq5409 X0
       grind)
    | exact resolve eq5409 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5409
  have eq5511 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5461 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5461
    | (have j0 := eq5461 X0
       grind)
    | exact resolve eq5461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461
  have eq5578 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5511 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq5511
    | exact resolve eq5511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511
  have eq5660 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5578 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5578
    | (have j0 := eq5578 X0
       grind)
    | exact resolve eq5578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5578
  have eq6291 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ (k (τ X0) (τ X0))) = (τ (k (k (τ X0) (τ X0)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5243 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5243
    | (have j0 := eq5243 (τ X0) X1
       grind)
    | exact resolve eq5243 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5243
  have eq6357 : ∀ X0 X1 : G, (τ (τ (k X0 X0))) = (τ (k (τ (k X0 X0)) (τ X0))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6291 X0 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq6291
    | (have j0 := eq6291 X0 X1
       grind)
    | exact resolve eq6291 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6291
  have eq6358 : ∀ X0 X1 : G, (τ (τ (k X0 X0))) = (τ (τ (k (k X0 X0) X0))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6357 X0 X1
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq6357
    | (have j0 := eq6357 X0 X1
       grind)
    | exact resolve eq6357 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6357
  have eq7771 : ∀ X0 X1 : G, (τ (k (k X0 X0) X0)) = (σ (τ (τ (k X0 X0)))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (τ (k (k X0 X0) X0))
       have i₂ := eq6358 X0 X1
       grind)
    | exact superpose eq6358 eq11
    | (have j1 := eq6358 X0 X1
       grind)
    | exact resolve eq11 eq6358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6358
  have eq7878 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7771 X0 X1
       have i₂ := eq11 (τ (k X0 X0))
       grind)
    | exact superpose eq11 eq7771
    | (have j0 := eq7771 X0 X1
       grind)
    | exact resolve eq7771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7771
  have eq7920 : ∀ X0 X1 : G, (k (k X0 X0) X0) = (σ (τ (k X0 X0))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (k X0 X0) X0)
       have i₂ := eq7878 X0 X1
       grind)
    | exact superpose eq7878 eq11
    | (have j1 := eq7878 X0 X1
       grind)
    | exact resolve eq11 eq7878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7878
  have eq8027 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7920 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq7920
    | (have j0 := eq7920 X0 X1
       grind)
    | exact resolve eq7920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7920
  have eq8089 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq8027 (τ X0) X1
       grind)
    | exact superpose eq8027 eq19
    | (have j1 := eq8027 (τ X0) X1
       grind)
    | exact resolve eq19 eq8027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8027
  have eq8127 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8089 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq8089
    | (have j0 := eq8089 X0 X1
       grind)
    | exact resolve eq8089 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8089
  have eq8167 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8127 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8127
    | (have j0 := eq8127 X0 X1
       grind)
    | exact resolve eq8127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8127
  have eq8486 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    grind
  clear eq8167
  have eq8487 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8486 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq8486
    | (have j0 := eq8486 X0
       grind)
    | exact resolve eq8486 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8486
  have eq12213 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq8487 X0
       grind)
    | exact superpose eq8487 eq78
    | (have j1 := eq8487 X0
       grind)
    | exact resolve eq78 eq8487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq8487
  have eq12264 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12213 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq12213
    | (have j0 := eq12213 X0
       grind)
    | exact resolve eq12213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12213
  have eq12265 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12264 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12264
  have eq12828 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq810 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq810
    | exact resolve eq810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq12951 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12828 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq12828
    | (have j0 := eq12828 X0
       grind)
    | exact resolve eq12828 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12828
  have eq12977 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (σ (k (k (τ X0) (τ X0)) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12951 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12951
    | (have j0 := eq12951 X0
       grind)
    | exact resolve eq12951 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12951
  have eq12984 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12977 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq12977
    | (have j0 := eq12977 X0
       grind)
    | exact resolve eq12977 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12977
  have eq12989 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12984 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq12984
    | (have j0 := eq12984 X0
       grind)
    | exact resolve eq12984 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq12984
  have eq12990 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12989 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12989
    | (have j0 := eq12989 X0
       grind)
    | exact resolve eq12989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12989
  have eq12991 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12990 X0
       have i₂ := eq12265 X0
       grind)
    | exact superpose eq12265 eq12990
    | (have j0 := eq12990 X0
       grind)
    | exact resolve eq12990 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12990
  have eq13003 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (k X0 X0) X1
       have i₂ := eq12991 X0
       grind)
    | exact superpose eq12991 eq68
    | (have j1 := eq12991 X0
       grind)
    | exact resolve eq68 eq12991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12991
  have eq13185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 X0 X0 X0
       have i₂ := eq13003 X0 X1
       grind)
    | exact superpose eq13003 eq90
    | (have j1 := eq13003 X0 X2
       grind)
    | exact resolve eq90 eq13003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13003
  have eq13255 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13185 X0 X1 X2
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq13185
    | (have j0 := eq13185 X0 X1 X2
       grind)
    | exact resolve eq13185 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13185
  have eq13617 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13255 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13255
  have eq13618 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13617
  have eq13661 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 (k X0 X0) X0 X0
       have i₂ := eq13618 X0
       grind)
    | exact superpose eq13618 eq65
    | exact resolve eq65 eq13618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq13618
  have eq13723 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13661 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq13661
    | exact resolve eq13661 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13724 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq13661 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq13661
    | exact resolve eq13661 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13661
  have eq13904 : ∀ X0 X1 : G, (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ (k X0 X0)) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ (k X0 X0)) (σ X0)
       have i₂ := eq13723 X0
       grind)
    | exact superpose eq13723 eq90
    | exact resolve eq90 eq13723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14030 : ∀ X0 X1 : G, (M.op (M.op (τ (k X0 X0)) X1) (τ X0)) = (M.op X1 (M.op (M.op (τ (k X0 X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (τ (k X0 X0)) (τ X0)
       have i₂ := eq13724 X0
       grind)
    | exact superpose eq13724 eq90
    | exact resolve eq90 eq13724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13724
  have eq22305 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq588 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq588
    | exact resolve eq588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq22435 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22305 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq22305
    | (have j0 := eq22305 X0 X1
       grind)
    | exact resolve eq22305 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22305
  have eq25916 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5660 X0
       have i₂ := eq22435 X0 X0
       grind)
    | exact superpose eq22435 eq5660
    | (have j1 := eq22435 X0 X0
       grind)
    | exact resolve eq5660 eq22435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5660
  have eq26046 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25916
  have eq26074 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26046 X0
       have i₂ := eq12265 X0
       grind)
    | exact superpose eq12265 eq26046
    | (have j0 := eq26046 X0
       grind)
    | exact resolve eq26046 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12265 eq26046
  have eq72957 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq26074 X0
       grind)
    | exact superpose eq26074 eq10
    | (have j1 := eq26074 X0
       grind)
    | exact resolve eq10 eq26074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26074
  have eq73077 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq72957 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72957
    | (have j0 := eq72957 X0
       grind)
    | exact resolve eq72957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72957
  have eq73078 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq73077 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73077
  have eq73200 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq73078 X0
       grind)
    | exact superpose eq73078 eq10
    | (have j1 := eq73078 X0
       grind)
    | exact resolve eq10 eq73078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73078
  have eq73306 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq73200 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq73200
    | (have j0 := eq73200 X0
       grind)
    | exact resolve eq73200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73200
  have eq73396 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq73306
  have eq73666 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq73396 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73396
  have eq73871 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13723 X0
       have i₂ := eq73666 X0
       grind)
    | exact superpose eq73666 eq13723
    | exact resolve eq13723 eq73666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13723
  have eq73892 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13904 X0 X1
       have i₂ := eq73666 X0
       grind)
    | exact superpose eq73666 eq13904
    | exact resolve eq13904 eq73666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13904
  have eq73910 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) = (M.op X1 (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14030 X0 X1
       have i₂ := eq73666 X0
       grind)
    | exact superpose eq73666 eq14030
    | exact resolve eq14030 eq73666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14030
  have eq73986 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq73666 (σ X0)
       grind)
    | exact superpose eq73666 eq15
    | exact resolve eq15 eq73666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74067 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73986 X0
       have i₂ := eq73666 X0
       grind)
    | exact superpose eq73666 eq73986
    | exact resolve eq73986 eq73666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73666 eq73986
  have eq209146 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq587 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq587
    | exact resolve eq587 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq209991 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq209146 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq209146
    | (have j0 := eq209146 X0 X1
       grind)
    | exact resolve eq209146 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq209146
  have eq210516 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209991 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq209991
    | (have j0 := eq209991 (σ X1) (σ X0)
       grind)
    | exact resolve eq209991 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209991
  have eq211191 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210516 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq210516
    | (have j0 := eq210516 X0 X1
       grind)
    | exact resolve eq210516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210516
  have eq211255 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211191 X0 X1
       have i₂ := eq74067 X1
       grind)
    | exact superpose eq74067 eq211191
    | (have j0 := eq211191 X0 X1
       grind)
    | exact resolve eq211191 eq74067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74067 eq211191
  have eq954962 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq211255 X0 X1
       grind)
    | exact superpose eq211255 eq11
    | (have j1 := eq211255 X0 X1
       grind)
    | exact resolve eq11 eq211255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211255
  have eq985568 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq954962 y x
       grind)
    | exact superpose eq954962 eq16
    | (have j1 := eq954962 y x
       grind)
    | exact resolve eq16 eq954962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954962
  have eq989165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq985568
       have i₂ := eq22435 x y
       grind)
    | exact superpose eq22435 eq985568
    | (have j1 := eq22435 x y
       grind)
    | (have r₁ := eq985568
       have r₂ := eq22435 x y
       grind)
    | exact resolve eq985568 eq22435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22435 eq985568
  have eq989166 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq989165
  have eq1036819 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 y x
       have i₂ := eq989166
       grind)
    | exact superpose eq989166 eq66
    | exact resolve eq66 eq989166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989166
  have eq1052350 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq68 (σ y) (σ x) X0
       have i₂ := eq1036819
       grind)
    | exact superpose eq1036819 eq68
    | exact resolve eq68 eq1036819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1036819
  have eq1053025 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1052350 X0
       have i₂ := eq64 (σ y) X0
       grind)
    | exact superpose eq64 eq1052350
    | exact resolve eq1052350 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052350
  have eq1053481 : ∀ X0 : G, (M.op x x) = (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1053025 X0
       grind)
    | exact superpose eq1053025 eq10
    | (have j1 := eq1053025 X0
       grind)
    | exact resolve eq10 eq1053025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053025
  have eq1054043 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1053481 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1053481
    | (have j0 := eq1053481 X0
       grind)
    | exact resolve eq1053481 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053481
  have eq1054044 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op x x) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1054043 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054043
  have eq1054394 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x x) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 y y
       have i₂ := eq1054044 X0
       grind)
    | exact superpose eq1054044 eq90
    | (have j1 := eq1054044 X1
       grind)
    | exact resolve eq90 eq1054044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1054044
  have eq1054787 : ∀ X0 X1 : G, y = (M.op x x) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1054394 X1 X1
       have i₂ := eq64 y X1
       grind)
    | exact superpose eq64 eq1054394
    | (have j0 := eq1054394 X0 X1
       grind)
    | exact resolve eq1054394 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054394
  have eq1055119 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73871 x
       have i₂ := eq1054787 X0 X1
       grind)
    | exact superpose eq1054787 eq73871
    | (have j1 := eq1054787 X0 (σ x)
       grind)
    | exact resolve eq73871 eq1054787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73871
  have eq1055411 : ∀ X0 X1 : G, y = (M.op x y) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 x x
       have i₂ := eq1054787 X0 X1
       grind)
    | exact superpose eq1054787 eq66
    | (have j1 := eq1054787 x X1
       grind)
    | exact resolve eq66 eq1054787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1054787
  have eq1057662 : ∀ X0 : G, y ≠ y ∨ y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1055411 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055411
  have eq1057663 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1057662 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057662
  have eq1072842 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ y = (M.op X0 y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1055119 X0 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055119
  have eq1072843 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1072842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072842
  have eq1072972 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq64 (σ y) (σ x)
       have i₂ := eq1072843 X0
       grind)
    | exact superpose eq1072843 eq64
    | (have j1 := eq1072843 X0
       grind)
    | exact resolve eq64 eq1072843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072843
  have eq1073374 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1072972 X0
       grind)
    | exact superpose eq1072972 eq16
    | (have j1 := eq1072972 X0
       grind)
    | exact resolve eq16 eq1072972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072972
  have eq1073841 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1073374 X0
       have i₂ := eq1057663 X1
       grind)
    | exact superpose eq1057663 eq1073374
    | (have j0 := eq1073374 X0
       have j1 := eq1057663 X1
       grind)
    | exact resolve eq1073374 eq1057663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057663 eq1073374
  have eq1073844 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have j0 := eq1073841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073841
  have eq1073967 : ∀ X0 X1 : G, (M.op (M.op (τ (σ y)) X0) (τ (σ y))) = (M.op X0 (M.op (M.op (τ (σ y)) X0) (τ (σ y)))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq73910 (σ y) X1
       have i₂ := eq1073844 X0 (σ y)
       grind)
    | exact superpose eq1073844 eq73910
    | (have j1 := eq1073844 X1 X1
       grind)
    | exact resolve eq73910 eq1073844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73910 eq1073844
  have eq1074730 : ∀ X0 X1 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1073967 X1 X1
       have i₂ := eq64 (τ (σ y)) X1
       grind)
    | exact superpose eq64 eq1073967
    | (have j0 := eq1073967 X0 X1
       grind)
    | exact resolve eq1073967 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073967
  have eq1074857 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1074730 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1074730
    | (have j0 := eq1074730 X0 X0
       grind)
    | exact resolve eq1074730 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074730
  have eq1077313 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1074857 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074857
  have eq1077314 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1077313 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077313
  have eq1077359 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73892 y x
       have i₂ := eq1077314 y
       grind)
    | exact superpose eq1077314 eq73892
    | exact resolve eq73892 eq1077314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73892
  have eq1079290 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1077359 x
       have i₂ := eq64 (σ y) x
       grind)
    | exact superpose eq64 eq1077359
    | exact resolve eq1077359 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1077359
  have eq1088450 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1079290 (σ x)
       grind)
    | exact superpose eq1079290 eq16
    | exact resolve eq16 eq1079290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079290
  have eq1088838 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1088450
       have i₂ := eq1077314 x
       grind)
    | exact superpose eq1077314 eq1088450
    | exact resolve eq1088450 eq1077314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077314 eq1088450
  have eq1088839 : False := by grind
  exact eq1088839

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pxy_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (τ X0) (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq110
    | exact resolve eq110 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (M.op X0 X1) X0
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq110
    | exact resolve eq110 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq9
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq150 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq9
    | exact resolve eq9 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq116 X1 X2 X0
       grind)
    | exact superpose eq116 eq110
    | exact resolve eq110 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (M.op (M.op (σ X1) X0) (σ (M.op X1 X1))) = (M.op X0 (M.op (M.op (σ X1) X0) (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (M.op (M.op (σ X1) X0) (σ (M.op X1 X1))) X0
       have i₂ := eq134 X1 X0
       grind)
    | exact superpose eq134 eq110
    | exact resolve eq110 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq410 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq412 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
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
  have eq547 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq410 x y
       grind)
    | exact superpose eq410 eq16
    | (have j1 := eq410 x y
       grind)
    | exact resolve eq16 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq21141 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq412 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq412
    | exact resolve eq412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq21266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21141 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq21141
    | (have j0 := eq21141 X0 X1
       grind)
    | exact resolve eq21141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21141
  have eq35414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq547
       have i₂ := eq21266 x y
       grind)
    | exact superpose eq21266 eq547
    | (have j1 := eq21266 (σ x) (σ y)
       grind)
    | (have r₁ := eq547
       have r₂ := eq21266 x y
       grind)
    | (have r₁ := eq547
       have r₂ := eq21266 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq547
       have r₂ := eq21266 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq547 eq21266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq21266
  have eq35415 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq35414
  have eq330443 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35415
       grind)
    | exact superpose eq35415 eq16
    | exact resolve eq16 eq35415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35415
  have eq330444 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq330443
       have r₂ := eq22 x
       grind)
    | exact resolve eq330443 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330443
  have eq330451 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq114 y x
       have i₂ := eq330444
       grind)
    | exact superpose eq330444 eq114
    | exact resolve eq114 eq330444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq330444
  have eq330587 : y = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq330451
       grind)
    | exact superpose eq330451 eq10
    | exact resolve eq10 eq330451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330451
  have eq330739 : x = y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq330587
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq330587
    | exact resolve eq330587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330587
  have eq330741 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq330739
       grind)
    | exact superpose eq330739 eq16
    | exact resolve eq16 eq330739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330739
  have eq330742 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq330741
       have r₂ := eq22 x
       grind)
    | exact resolve eq330741 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq330741
  have eq330772 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq116 (σ y) (σ x) X0
       have i₂ := eq330742
       grind)
    | exact superpose eq330742 eq116
    | exact resolve eq116 eq330742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq330742
  have eq330899 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq330772 X0
       have i₂ := eq110 (σ y) X0
       grind)
    | exact superpose eq110 eq330772
    | exact resolve eq330772 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330772
  have eq331453 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 y y
       have i₂ := eq330899 X0
       grind)
    | exact superpose eq330899 eq176
    | (have j1 := eq330899 X1
       grind)
    | exact resolve eq176 eq330899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330899
  have eq331533 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq331453 X1 X1
       have i₂ := eq110 y X1
       grind)
    | exact superpose eq110 eq331453
    | (have j0 := eq331453 X0 X1
       grind)
    | exact resolve eq331453 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331453
  have eq332073 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ y)) X0) (τ (σ y))) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (σ y) X0
       have i₂ := eq331533 X1 (σ y)
       grind)
    | exact superpose eq331533 eq150
    | (have j1 := eq331533 X1 X1
       grind)
    | exact resolve eq150 eq331533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq331533
  have eq333078 : ∀ X0 X1 : G, (M.op (τ (σ y)) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq332073 X0 X1
       have i₂ := eq110 (τ (σ y)) X0
       grind)
    | exact superpose eq110 eq332073
    | (have j0 := eq332073 X0 X1
       grind)
    | exact resolve eq332073 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332073
  have eq333410 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq333078 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq333078
    | (have j0 := eq333078 X0 X1
       grind)
    | exact resolve eq333078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333078
  have eq334583 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq333410 y y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333410
  have eq334584 : y = (M.op y y) := by grind
  clear eq334583
  have eq334731 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq277 X0 y
       have i₂ := eq334584
       grind)
    | exact superpose eq334584 eq277
    | exact resolve eq277 eq334584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq335230 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq176 X0 y y
       have i₂ := eq334584
       grind)
    | exact superpose eq334584 eq176
    | exact resolve eq176 eq334584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq334584
  have eq335310 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq335230 x
       have i₂ := eq110 y x
       grind)
    | exact superpose eq110 eq335230
    | exact resolve eq335230 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335230
  have eq335766 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq334731 x
       have i₂ := eq110 (σ y) x
       grind)
    | exact superpose eq110 eq334731
    | exact resolve eq334731 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq334731
  have eq342506 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq335766 (σ x)
       grind)
    | exact superpose eq335766 eq16
    | exact resolve eq16 eq335766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335766
  have eq342612 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq342506
       have i₂ := eq335310 x
       grind)
    | exact superpose eq335310 eq342506
    | exact resolve eq342506 eq335310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335310 eq342506
  have eq342613 : False := by grind
  exact eq342613

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = X2 ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq14
    | (have j0 := eq14 X2 X2
       grind)
    | exact resolve eq14 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq100 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq90 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq90 X0 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq90 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq297 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (k X4 X1) = (M.op X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq25 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq21 x X1 x X0
       grind)
    | exact superpose eq21 eq25
    | (have j0 := eq25 X0 X1 x X4
       grind)
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq308 : ∀ X1 X4 : G, (k X4 X1) = (M.op X4 X1) := by
    intro X1 X4
    first
    | (have j0 := eq297 x X1 X4
       have j1 := eq100 x X4 X1
       grind)
    | (have r₁ := eq297 x x X4
       have r₂ := eq100 x X1 x
       grind)
    | (have r₁ := eq297 x (M.op x (M.op x x)) X4
       have r₂ := eq100 x X1 (M.op x (M.op x x))
       grind)
    | (have r₁ := eq297 X1 (k X1 (M.op X1 X1)) X4
       have r₂ := eq100 x X1 (M.op X1 X1)
       grind)
    | exact resolve eq297 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq297
  have eq583 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq308 (σ X1) (σ X0)
       grind)
    | exact superpose eq308 eq15
    | exact resolve eq15 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq308 X1 X0
       grind)
    | exact superpose eq308 eq583
    | exact resolve eq583 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq583
  have eq591 : False := by grind
  exact eq591

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  clear eq22
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  clear eq44
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq111 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq233 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq52
    | exact resolve eq52 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq247 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq233
    | (have j0 := eq233 (σ x)
       grind)
    | exact resolve eq233 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq247
    | exact resolve eq247 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq263 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq259
  have eq264 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq263
    | exact resolve eq263 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq271 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq55
    | exact resolve eq55 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq275 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq291 : ∀ X1 : G, (M.op X1 X1) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq271 X1 X1
       have i₂ := eq14 sF2 X1 sF3
       grind)
    | exact superpose eq14 eq271
    | exact resolve eq271 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq264
       have i₂ := eq291 sF2
       grind)
    | exact superpose eq291 eq264
    | exact resolve eq264 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq291
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq344 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq320 (M.op x x)
       grind)
    | exact superpose eq320 eq14
    | exact resolve eq14 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq378 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq344
    | exact resolve eq344 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq344
  have eq395 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq428 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq395 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq395 (σ y)
       grind)
    | exact resolve eq13 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq439 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq466 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq439 eq111
    | exact resolve eq111 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq439
  have eq3286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3282
  have eq3289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3286
    | exact resolve eq3286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq3291 : y = (M.op x y) := by
    first
    | (have r₁ := eq3289
       have r₂ := eq27
       grind)
    | exact resolve eq3289 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq3294 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3291 eq20
    | exact resolve eq20 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3296 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq3291 eq51
    | exact resolve eq51 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3308 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3294
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3294
    | exact resolve eq3294 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3294
  have eq3309 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3308 eq26
    | exact resolve eq26 eq3308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3557 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3296 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3296
    | (have j0 := eq3296 x
       grind)
    | exact resolve eq3296 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq3643 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq3291 eq3557
    | exact resolve eq3557 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq3651 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3643
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3643
    | exact resolve eq3643 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3643
  have eq3652 : y = (M.op x x) := by
    first
    | exact superpose eq3291 eq3651
    | exact resolve eq3651 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3651
  have eq3653 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq3652
       have i₂ := eq275 x X0
       grind)
    | (have i₁ := eq3652
       have i₂ := eq275 X0 x
       grind)
    | exact superpose eq275 eq3652
    | exact resolve eq3652 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq3690 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq3291 eq466
    | exact resolve eq466 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq3291
  have eq3691 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq3690 X0
       have i₂ := eq3652
       grind)
    | exact superpose eq3652 eq3690
    | exact resolve eq3690 eq3652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652 eq3690
  have eq3825 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq3691 X0
       have i₂ := eq3653 y
       grind)
    | exact superpose eq3653 eq3691
    | exact resolve eq3691 eq3653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3653 eq3691
  have eq3836 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq3825 y
       grind)
    | exact superpose eq3825 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq3825 y
       grind)
    | exact resolve eq13 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3864 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq3836 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836
  have eq3875 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq3864 X0
       have i₂ := eq3825 X0
       grind)
    | exact superpose eq3825 eq3864
    | exact resolve eq3864 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3825 eq3864
  have eq3899 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq3875 (τ X0)
       grind)
    | exact superpose eq3875 eq34
    | exact resolve eq34 eq3875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3875
  have eq3904 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3899 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3899
    | (have j0 := eq3899 X0
       grind)
    | exact resolve eq3899 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3899
  have eq3908 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3308 eq3904
    | exact resolve eq3904 eq3308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308 eq3904
  have eq3921 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3908 eq76
    | (have j0 := eq76 X0 (σ (M.op x y))
       grind)
    | exact resolve eq76 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3908
  have eq3923 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq3921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq3980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3923 eq3309
    | exact resolve eq3309 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309 eq3923
  have eq3983 : False := by grind
  exact eq3983

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq342 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq346 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq343 X0 X1
       grind)
    | (have r₁ := eq342 X0 X1
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq342 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq343
  have eq415 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq346
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq346 X0 X1
       grind)
    | exact superpose eq346 eq22
    | (have j1 := eq346 X0 X1
       grind)
    | exact resolve eq22 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq460 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq415 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq415 X0 X1
       grind)
    | exact resolve eq13 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq460 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq480 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq472 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq472 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq472 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq506 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq480 X0 (τ X1)
       grind)
    | exact superpose eq480 eq17
    | (have j1 := eq480 X0 (τ X1)
       grind)
    | exact resolve eq17 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq512 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq480 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq506 (τ X0) X1
       grind)
    | exact superpose eq506 eq18
    | (have j1 := eq506 (τ X0) X1
       grind)
    | exact resolve eq18 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq506
  have eq744 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq735
    | (have j0 := eq735 X0 X1
       grind)
    | exact resolve eq735 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq759 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq744 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq744
    | (have j0 := eq744 X0 X1
       grind)
    | exact resolve eq744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq762 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq759 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq759
    | (have j0 := eq759 X0 X1
       grind)
    | exact resolve eq759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq819 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq480 X0 X1
       grind)
    | exact superpose eq480 eq762
    | (have j0 := eq762 X0 X1
       have j1 := eq480 X0 X1
       grind)
    | exact resolve eq762 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq762
  have eq890 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq819 X0 X1
       have j1 := eq512 X1 X0
       grind)
    | (have r₁ := eq819 X1 X0
       have r₂ := eq512 X0 X1
       grind)
    | exact resolve eq819 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq819
  have eq924 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq890 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq890
    | (have j0 := eq890 X1 (σ X0)
       grind)
    | exact resolve eq890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq1340 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq924 X1 (σ X0)
       grind)
    | exact superpose eq924 eq22
    | (have j1 := eq924 X1 (σ X0)
       grind)
    | exact resolve eq22 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq924
  have eq1353 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1340 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1340
    | (have j0 := eq1340 X0 X1
       grind)
    | exact resolve eq1340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1371 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1353 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1353
    | (have j0 := eq1353 X0 X1
       grind)
    | exact resolve eq1353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1380 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1371 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1371
    | (have j0 := eq1371 X0 X1
       grind)
    | exact resolve eq1371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1401 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1380 x y
       grind)
    | exact superpose eq1380 eq16
    | (have j1 := eq1380 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1380 x y
       grind)
    | exact resolve eq16 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq1422 : x = (k y x) := by grind
  clear eq1401
  have eq1657 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq425 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq425
    | exact resolve eq425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq1706 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1657 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq1657
    | (have j0 := eq1657 X0 X1
       grind)
    | exact resolve eq1657 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1657
  have eq1743 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq1706 X0 (σ X1)
       grind)
    | exact superpose eq1706 eq28
    | (have j1 := eq1706 X0 (σ X1)
       grind)
    | exact resolve eq28 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1706
  have eq1809 : (σ (M.op x y)) ≠ (σ x) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1743 (σ x) y
       grind)
    | exact superpose eq1743 eq16
    | (have j1 := eq1743 (σ x) y
       grind)
    | exact resolve eq16 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1823 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1809
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1809
    | exact resolve eq1809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1838 : (σ (M.op x y)) ≠ (σ x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1823
       have i₂ := eq1422
       grind)
    | exact superpose eq1422 eq1823
    | exact resolve eq1823 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823
  have eq1867 : (σ x) ≠ (σ x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1838
       have i₂ := eq415 x y
       grind)
    | exact superpose eq415 eq1838
    | (have j1 := eq415 x y
       grind)
    | exact resolve eq1838 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1868 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y x) := by grind
  clear eq1867
  have eq1870 : x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1868
       have i₂ := eq1422
       grind)
    | exact superpose eq1422 eq1868
    | exact resolve eq1868 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868
  have eq1871 : (σ x) ≠ (σ x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1838
       have i₂ := eq1870
       grind)
    | exact superpose eq1870 eq1838
    | exact resolve eq1838 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838 eq1870
  have eq1879 : (σ x) ≠ (σ x) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1871
  have eq1880 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1879
  have eq1890 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq1880
       grind)
    | exact superpose eq1880 eq11
    | exact resolve eq11 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq1916 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1890
       grind)
    | exact superpose eq1890 eq16
    | exact resolve eq16 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq1962 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1916
       have i₂ := eq415 x y
       grind)
    | exact superpose eq415 eq1916
    | (have j1 := eq415 x y
       grind)
    | exact resolve eq1916 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq1963 : (M.op x y) = (k y x) := by grind
  clear eq1962
  have eq1966 : x = (M.op x y) := by
    first
    | (have i₁ := eq1963
       have i₂ := eq1422
       grind)
    | exact superpose eq1422 eq1963
    | exact resolve eq1963 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq1963
  have eq1967 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1916
       have i₂ := eq1966
       grind)
    | exact superpose eq1966 eq1916
    | exact resolve eq1916 eq1966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916 eq1966
  have eq1978 : False := by grind
  exact eq1978

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_x_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq268 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq269 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq269 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq284
    | exact resolve eq284 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq284
  have eq347 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq347 X0 X1
       have j1 := eq348 X0 X1
       grind)
    | (have r₁ := eq347 X0 X1
       have r₂ := eq348 X0 X1
       grind)
    | exact resolve eq347 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq368 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq349 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq349
    | exact resolve eq349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq349 X0 (σ X1)
       grind)
    | exact superpose eq349 eq15
    | (have j1 := eq349 X0 (σ X1)
       grind)
    | exact resolve eq15 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq398 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 X1
       have i₂ := eq303 X1
       grind)
    | exact superpose eq303 eq379
    | (have j0 := eq379 X0 X1
       grind)
    | exact resolve eq379 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq379
  have eq416 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq368 (τ X0) X1
       grind)
    | exact superpose eq368 eq19
    | (have j1 := eq368 (τ X0) X1
       grind)
    | exact resolve eq19 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq368
  have eq553 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq416 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq416
    | exact resolve eq416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq594 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq852 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq398 x y
       grind)
    | exact superpose eq398 eq16
    | (have j1 := eq398 x y
       grind)
    | exact resolve eq16 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq887 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq852
       have i₂ := eq594 x y
       grind)
    | exact superpose eq594 eq852
    | (have j1 := eq594 x y
       grind)
    | (have r₁ := eq852
       have r₂ := eq594 x y
       grind)
    | exact resolve eq852 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq888 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq887
  have eq896 : x = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq888
       grind)
    | exact superpose eq888 eq9
    | exact resolve eq9 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq901 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq896
       grind)
    | exact resolve eq12 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq903 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq852
       have i₂ := eq903 y
       grind)
    | exact superpose eq903 eq852
    | exact resolve eq852 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq903
  have eq915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq914
  have eq916 : (σ x) = (σ (M.op y y)) := by grind
  clear eq915
  have eq919 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq10
    | exact resolve eq10 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq963 : x = (M.op y y) := by
    first
    | (have i₁ := eq919
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq919
    | exact resolve eq919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq977 : x = (M.op x x) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq963
       grind)
    | exact superpose eq963 eq9
    | exact resolve eq9 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq980 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq348 x X0
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq348
    | (have j0 := eq348 x X0
       grind)
    | exact resolve eq348 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq981 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq977
       grind)
    | exact resolve eq12 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq983 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq981 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq984 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq980 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1063 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq984 (σ X0)
       grind)
    | exact superpose eq984 eq15
    | exact resolve eq15 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1083 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1063 X0
       have i₂ := eq983 X0
       grind)
    | exact superpose eq983 eq1063
    | exact resolve eq1063 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq1063
  have eq1227 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1083 y
       grind)
    | exact superpose eq1083 eq16
    | (have r₁ := eq16
       have r₂ := eq1083 y
       grind)
    | exact resolve eq16 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1237 : False := by grind
  exact eq1237

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if X = Y then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxx_pxx_x_Equation3735 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law3735 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
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
  clear eq23 eq36
  have eq51 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X2) X3 (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op y x) = (M.op (M.op y X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op X1 X0) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X0 X2) (M.op X1 X0)) = (M.op (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X2) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X2) (M.op X1 X0)
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op X1 X0)
       have r₂ := eq14 X0 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq78 (σ X0)
       grind)
    | exact superpose eq78 eq10
    | exact resolve eq10 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq44
    | exact resolve eq44 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq84 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq78 sF2
       grind)
    | exact superpose eq78 eq81
    | exact resolve eq81 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq80
    | exact resolve eq80 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq92 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq78 sF3
       grind)
    | exact superpose eq78 eq76
    | exact resolve eq76 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq78 y
       grind)
    | exact superpose eq78 eq92
    | exact resolve eq92 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq129 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq38 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq38
    | exact resolve eq38 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
       have i₂ := eq78 sF1
       grind)
    | exact superpose eq78 eq139
    | exact resolve eq139 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq78 sF0
       grind)
    | exact superpose eq78 eq142
    | exact resolve eq142 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq167 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (σ (k (M.op y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq41
    | exact resolve eq41 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq93
  have eq243 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq78 (τ X0)
       grind)
    | exact superpose eq78 eq35
    | exact resolve eq35 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) (M.op x y))) = (k (k X0 (σ X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq42
    | exact resolve eq42 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq306 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq294 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq294
    | exact resolve eq294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq308 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq306 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq306
    | exact resolve eq306 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq500 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) x
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq14
    | exact resolve eq14 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) (M.op X2 (M.op (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (σ X0) (σ X0) X1 X2
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq53
    | exact resolve eq53 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq602 X0 X1 X2 x
       have i₂ := eq14 X1 X0 x
       grind)
    | exact superpose eq14 eq602
    | exact resolve eq602 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq697 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) (M.op X1 X0)) ∨ (k (M.op X0 X1) (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X1 X3)
       have i₂ := eq56 X1 X0 X3 X2
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 (M.op X0 X1) (M.op X1 X3)
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X0) (M.op X0 X2)) (M.op X0 X1)
       have r₂ := eq56 X0 X1 X2 (M.op X0 X2)
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) = (M.op (M.op X1 X4) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 X4 X0 (M.op (M.op X0 X1) X3)
       have i₂ := eq56 X1 X0 X2 X3
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq702 X0 X1 X2 X3 x
       have i₂ := eq53 X1 x X2 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq702
    | exact resolve eq702 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq727 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq708 X0 X1 x X3
       have i₂ := eq14 X1 X0 x
       grind)
    | exact superpose eq14 eq708
    | exact resolve eq708 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq773 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq308 X0
       grind)
    | exact superpose eq308 eq16
    | exact resolve eq16 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq1036 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1048 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (M.op x X1) (M.op y x)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq243
    | exact resolve eq243 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1064 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1048 X0 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq1048
    | exact resolve eq1048 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1065 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1064 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1064
    | (have j0 := eq1064 X0
       grind)
    | exact resolve eq1064 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1069 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq1065 eq13
    | (have j0 := eq13 (M.op x y) (M.op y X0)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op y X0)
       have r₂ := eq1065 X0
       grind)
    | exact resolve eq13 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq1069 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1087 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) X1) (M.op (σ y) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq246
    | exact resolve eq246 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1103 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1087 X0 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq1087
    | exact resolve eq1087 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1104 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq1103
    | (have j0 := eq1103 X0
       grind)
    | exact resolve eq1103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1103
  have eq1108 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq1104 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (M.op (σ y) X0)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ y) X0)
       have r₂ := eq1104 X0
       grind)
    | exact resolve eq13 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq1108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1265 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq612 X2 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X2 X1 X2
       grind)
    | exact superpose eq53 eq612
    | exact resolve eq612 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1268 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq243 eq612
    | exact resolve eq612 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq1269 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq246 eq612
    | exact resolve eq612 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq1301 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq1065 eq1268
    | exact resolve eq1268 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1310 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 X1) (M.op x X0)) := by
    intro X0 X1
    first
    | exact superpose eq1268 eq14
    | exact resolve eq14 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq1268 eq51
    | exact resolve eq51 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq51 eq1322
    | exact resolve eq1322 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1343 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1310 X0 x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq1310
    | exact resolve eq1310 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1352 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq1104 eq1269
    | exact resolve eq1269 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1376 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1269 eq52
    | exact resolve eq52 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq52 eq1376
    | exact resolve eq1376 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1376
  have eq1503 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1343 eq144
    | exact resolve eq144 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq1343
  have eq1511 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1268 eq1503
    | exact resolve eq1503 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1521 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1511
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq1511
    | exact resolve eq1511 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1645 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) (M.op X1 (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq1269 eq591
    | exact resolve eq591 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq1908 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq1521 eq1265
    | exact resolve eq1265 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1916 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1265 X0 X1 (M.op X1 X2)
       have i₂ := eq612 X1 X0 X2
       grind)
    | exact superpose eq612 eq1265
    | exact resolve eq1265 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2005 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1908 x
       have i₂ := eq1265 sF1 sF1 x
       grind)
    | exact superpose eq1265 eq1908
    | exact resolve eq1908 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq2049 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq1352 eq2005
    | exact resolve eq2005 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq2514 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ (M.op x y)) (M.op X1 (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq2005 eq1645
    | exact resolve eq1645 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq2515 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) X0) X1) = (M.op (σ (M.op x y)) (M.op X1 (M.op (σ (M.op x y)) X0))) := by
    intro X0 X1
    first
    | exact superpose eq2005 eq2514
    | exact resolve eq2514 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005 eq2514
  have eq2516 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X1) = (M.op (σ (M.op x y)) (M.op X1 (M.op (σ (M.op x y)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2515 X1 x
       have i₂ := eq1265 sF1 X1 x
       grind)
    | exact superpose eq1265 eq2515
    | exact resolve eq2515 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515
  have eq2556 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) = (M.op (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) (M.op (M.op (σ (M.op x y)) X0) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2516 eq727
    | exact resolve eq727 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq2516
  have eq2560 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (M.op (M.op (σ (M.op x y)) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2556 X0 X1 X2
       have i₂ := eq1265 (M.op X0 (M.op sF1 X1)) sF1 (M.op (M.op sF1 X0) X2)
       grind)
    | exact superpose eq1265 eq2556
    | exact resolve eq2556 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556
  have eq2583 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) = (M.op X0 (M.op (M.op (σ (M.op x y)) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2560 X0 X1 X2
       have i₂ := eq1265 X0 (M.op sF1 X1) (M.op (M.op sF1 X0) X2)
       grind)
    | exact superpose eq1265 eq2560
    | exact resolve eq2560 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq2598 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ (M.op x y)) X2)) = (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2583 X1 X1 X2
       have i₂ := eq1265 sF1 X1 X2
       grind)
    | exact superpose eq1265 eq2583
    | exact resolve eq2583 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583
  have eq2603 : ∀ X0 X2 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2598 X0 x X2
       have i₂ := eq1265 X0 (M.op sF1 x) sF1
       grind)
    | exact superpose eq1265 eq2598
    | exact resolve eq2598 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq3231 : ∀ X0 X1 : G, (σ (k (τ X0) (M.op x y))) = (k (k X0 (σ X1)) (σ (M.op x y))) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq304
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq3256 : ∀ X0 X1 : G, (k (k X0 (σ X1)) (σ (M.op x y))) = (k X0 (σ (M.op x y))) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3231 X0 X1
       have i₂ := eq35 X0 sF0
       grind)
    | exact superpose eq35 eq3231
    | (have j0 := eq3231 X0 X1
       grind)
    | exact resolve eq3231 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq3270 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = (k (k X0 (σ X1)) (σ (M.op x y))) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq21 eq3256
    | (have j0 := eq3256 X0 X1
       grind)
    | exact resolve eq3256 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3874 : ∀ X0 : G, (M.op x (M.op x y)) = (k (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq1268 eq1079
    | exact resolve eq1079 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq3875 : ∀ X0 : G, (M.op x x) = (k (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq1334 eq3874
    | exact resolve eq3874 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874
  have eq3945 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1269 eq1118
    | exact resolve eq1118 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq1269
  have eq3946 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq1381 eq3945
    | exact resolve eq3945 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381 eq3945
  have eq3947 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq1521 eq3946
    | exact resolve eq3946 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3946
  have eq4019 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq500 X0 x
       have i₂ := eq1265 (σ X0) x (σ (M.op X0 X0))
       grind)
    | exact superpose eq1265 eq500
    | exact resolve eq500 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq4079 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94 X0 (M.op X0 X0)
       have i₂ := eq4019 X0
       grind)
    | exact superpose eq4019 eq94
    | (have j0 := eq94 X0 (M.op X0 X0)
       grind)
    | exact resolve eq94 eq4019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq4019
  have eq4098 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4079 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4079
  have eq5275 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X1 X0)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1036 X0 X1
       have i₂ := eq1265 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1265 eq1036
    | exact resolve eq1036 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq5276 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5275 X0 X1
       have i₂ := eq1916 X0 X0 X1
       grind)
    | exact superpose eq1916 eq5275
    | exact resolve eq5275 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5275
  have eq8174 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq588 X0 X1 X2
       have i₂ := eq1916 (σ (M.op X0 X0)) X2 (M.op (σ X0) X1)
       grind)
    | exact superpose eq1916 eq588
    | exact resolve eq588 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq8175 : ∀ X0 X2 : G, (M.op (σ X0) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq8174 X0 x X2
       have i₂ := eq1265 (σ X0) x X2
       grind)
    | exact superpose eq1265 eq8174
    | exact resolve eq8174 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8174
  have eq8219 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) X1
       have i₂ := eq8175 X0 X1
       grind)
    | exact superpose eq8175 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) X1
       grind)
    | exact resolve eq13 eq8175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8175
  have eq8296 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8219 X0 X1
       have i₂ := eq85 (M.op X0 X0)
       grind)
    | exact superpose eq85 eq8219
    | (have j0 := eq8219 X0 X1
       grind)
    | (have r₁ := eq8219 X0 (σ X0)
       have r₂ := eq85 X0
       grind)
    | exact resolve eq8219 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8219
  have eq8350 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8296 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq8296
    | (have j0 := eq8296 X0 X1
       grind)
    | exact resolve eq8296 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8296
  have eq15878 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 X0)) ∨ (k (M.op X0 X1) (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq697 X0 X1 x X3
       have i₂ := eq1265 (M.op X0 X1) x (M.op X1 X0)
       grind)
    | exact superpose eq1265 eq697
    | (have j0 := eq697 X0 X1 x X3
       grind)
    | exact resolve eq697 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq15879 : ∀ X0 X1 X3 : G, (k (M.op X0 X1) (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have j0 := eq15878 X0 X1 X3
       grind)
    | (have r₁ := eq15878 X0 x X3
       have r₂ := eq14 X0 x x
       grind)
    | exact resolve eq15878 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15878
  have eq15880 : ∀ X0 X1 X3 : G, (k (M.op X0 X1) (M.op X1 X3)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq15879 X0 X1 X3
       have i₂ := eq1265 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1265 eq15879
    | exact resolve eq15879 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15879
  have eq15881 : ∀ X0 X1 X3 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq15880 X0 X1 X3
       have i₂ := eq1916 X0 X0 X1
       grind)
    | exact superpose eq1916 eq15880
    | exact resolve eq15880 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15880
  have eq16015 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq15881 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15881
    | (have j0 := eq15881 X0 x y
       grind)
    | exact resolve eq15881 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28594 : (σ (M.op x x)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3875 eq129
    | exact resolve eq129 eq3875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq3875
  have eq28595 : (M.op (σ x) (σ x)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq28594
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq28594
    | exact resolve eq28594 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq28594
  have eq28596 : (k (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1521 eq28595
    | exact resolve eq28595 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq28595
  have eq28928 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq28596 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq11 eq28596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28596
  have eq28929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2049 eq28928
    | exact resolve eq28928 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28928
  have eq28931 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq28929
       have r₂ := eq28
       grind)
    | exact resolve eq28929 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28929
  have eq28966 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28931 eq5276
    | exact resolve eq5276 eq28931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276 eq28931
  have eq28971 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq28966
       have i₂ := eq78 sF1
       grind)
    | exact superpose eq78 eq28966
    | exact resolve eq28966 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq28966
  have eq28972 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq28971
  have eq29007 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq28972 eq167
    | exact resolve eq167 eq28972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29076 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq28972 eq15881
    | exact resolve eq15881 eq28972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15881
  have eq29125 : (τ (σ (M.op x y))) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1268 eq29007
    | exact resolve eq29007 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29007
  have eq29130 : (τ (σ (M.op x y))) = (M.op x x) := by
    first
    | exact superpose eq1334 eq29125
    | exact resolve eq29125 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29125
  have eq29134 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31 eq29130
    | exact resolve eq29130 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq29130
  have eq29691 : ∀ X0 : G, (k (M.op X0 x) (M.op x y)) = (k (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq29076 X0
       have i₂ := eq16015 X0
       grind)
    | exact superpose eq16015 eq29076
    | exact resolve eq29076 eq16015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29711 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (M.op (σ X0) (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq29076 (σ X0)
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq29076
    | exact resolve eq29076 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq29715 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op (τ X0) (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq29076 (τ X0)
       have i₂ := eq773 X0
       grind)
    | exact superpose eq773 eq29076
    | exact resolve eq29076 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq29777 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k (M.op X0 (σ (M.op x y))) (σ (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1265 X0 X0 X1
       have i₂ := eq29076 X0
       grind)
    | exact superpose eq29076 eq1265
    | exact resolve eq1265 eq29076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30366 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (M.op (σ X0) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq29691 eq29711
    | exact resolve eq29711 eq29691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29711
  have eq30367 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op (τ X0) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq29691 eq29715
    | exact resolve eq29715 eq29691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29715
  have eq30374 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k (M.op X0 x) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq29691 eq29777
    | exact resolve eq29777 eq29691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29691 eq29777
  have eq30909 : ∀ X0 : G, (τ (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y)))) = (k (M.op (τ (M.op (σ (M.op x y)) X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2603 eq30367
    | exact resolve eq30367 eq2603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603 eq30367
  have eq31059 : ∀ X0 : G, (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (τ (M.op (σ (M.op x y)) X0)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq30909 x
       have i₂ := eq1265 sF1 x sF1
       grind)
    | exact superpose eq1265 eq30909
    | exact resolve eq30909 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq30909
  have eq31096 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op (τ (M.op (σ (M.op x y)) X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq167 eq31059
    | exact resolve eq31059 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq31059
  have eq31116 : ∀ X0 : G, (M.op x (M.op x y)) = (k (M.op (τ (M.op (σ (M.op x y)) X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1268 eq31096
    | exact resolve eq31096 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31096
  have eq31128 : ∀ X0 : G, (M.op x x) = (k (M.op (τ (M.op (σ (M.op x y)) X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1334 eq31116
    | exact resolve eq31116 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334 eq31116
  have eq31135 : ∀ X0 : G, (M.op x y) = (k (M.op (τ (M.op (σ (M.op x y)) X0)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq31128 X0
       have i₂ := eq29134
       grind)
    | exact superpose eq29134 eq31128
    | exact resolve eq31128 eq29134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31128
  have eq31330 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (τ (M.op (σ (M.op x y)) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq31135 eq30374
    | exact resolve eq30374 eq31135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30374 eq31135
  have eq31545 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op (σ (M.op x y)) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq1268 eq31330
    | exact resolve eq31330 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268 eq31330
  have eq32582 : ∀ X0 : G, (M.op x X0) = (M.op (τ (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2049 eq31545
    | exact resolve eq31545 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049 eq31545
  have eq33126 : (M.op (M.op x y) (M.op x x)) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32582 eq51
    | exact resolve eq51 eq32582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33178 : (M.op x x) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq51 eq33126
    | exact resolve eq33126 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq33126
  have eq33264 : (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq33178
       have i₂ := eq29134
       grind)
    | exact superpose eq29134 eq33178
    | exact resolve eq33178 eq29134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29134 eq33178
  have eq99340 : (σ (τ (M.op (σ x) (σ y)))) = (σ (k (τ (M.op (σ x) (σ y))) (M.op x (τ (M.op (σ x) (σ y)))))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (σ (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq32582 eq4098
    | exact resolve eq4098 eq32582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4098
  have eq99550 : (σ (τ (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) (σ (M.op x (τ (M.op (σ x) (σ y)))))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (σ (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq99340
       have i₂ := eq35 sF4 (M.op x (τ sF4))
       grind)
    | exact superpose eq35 eq99340
    | exact resolve eq99340 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq99340
  have eq99651 : (σ (τ (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (σ (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq33264 eq99550
    | exact resolve eq99550 eq33264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99550
  have eq99732 : (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (σ (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq21 eq99651
    | exact resolve eq99651 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99651
  have eq99793 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (σ (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq99732
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq99732
    | exact resolve eq99732 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99732
  have eq99838 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33264 eq99793
    | exact resolve eq99793 eq33264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33264 eq99793
  have eq99870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq99838
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq99838
    | exact resolve eq99838 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99838
  have eq99894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq99870
    | exact resolve eq99870 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99870
  have eq99914 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq99894
       have r₂ := eq28
       grind)
    | exact resolve eq99894 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99894
  have eq255225 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (k (M.op (σ X0) x) (M.op x y)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8350 X0 (σ X0)
       have i₂ := eq16015 (σ X0)
       grind)
    | exact superpose eq16015 eq8350
    | (have j0 := eq8350 X0 (σ X0)
       grind)
    | exact resolve eq8350 eq16015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8350 eq16015
  have eq255321 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq255225 X0
       grind)
    | (have r₁ := eq255225 X0
       have r₂ := eq30366 X0
       grind)
    | exact resolve eq255225 eq30366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30366 eq255225
  have eq255750 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq255321 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq255321
    | exact resolve eq255321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255321
  have eq258074 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16 (k (M.op X0 X0) X0)
       have i₂ := eq255750 X0
       grind)
    | exact superpose eq255750 eq16
    | exact resolve eq16 eq255750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255750
  have eq258284 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq258074 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq258074
    | exact resolve eq258074 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258074
  have eq271136 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k (k X0 (k (M.op (σ y) (σ y)) (σ y))) (σ (M.op x y))) ∨ (τ X0) = (k (M.op y y) y) ∨ (τ X0) = (M.op (τ X0) (k (M.op y y) y)) := by
    intro X0
    first
    | (have i₁ := eq3270 X0 (k (M.op y y) y)
       have i₂ := eq193
       grind)
    | exact superpose eq193 eq3270
    | (have j0 := eq3270 X0 (k (M.op y y) y)
       grind)
    | exact resolve eq3270 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq3270
  have eq271579 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k (k X0 (M.op (σ y) (σ y))) (σ (M.op x y))) ∨ (τ X0) = (k (M.op y y) y) ∨ (τ X0) = (M.op (τ X0) (k (M.op y y) y)) := by
    intro X0
    first
    | (have i₁ := eq271136 X0
       have i₂ := eq258284 sF3
       grind)
    | exact superpose eq258284 eq271136
    | (have j0 := eq271136 X0
       grind)
    | exact resolve eq271136 eq258284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271136
  have eq271770 : ∀ X0 : G, (τ X0) = (M.op y y) ∨ (k X0 (σ (M.op x y))) = (k (k X0 (M.op (σ y) (σ y))) (σ (M.op x y))) ∨ (τ X0) = (M.op (τ X0) (k (M.op y y) y)) := by
    intro X0
    first
    | (have i₁ := eq271579 X0
       have i₂ := eq258284 y
       grind)
    | exact superpose eq258284 eq271579
    | (have j0 := eq271579 X0
       grind)
    | exact resolve eq271579 eq258284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271579
  have eq271927 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op y y)) ∨ (τ X0) = (M.op y y) ∨ (k X0 (σ (M.op x y))) = (k (k X0 (M.op (σ y) (σ y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq271770 X0
       have i₂ := eq258284 y
       grind)
    | exact superpose eq258284 eq271770
    | (have j0 := eq271770 X0
       grind)
    | exact resolve eq271770 eq258284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258284 eq271770
  have eq272027 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k (k X0 (M.op (σ y) (σ y))) (σ (M.op x y))) ∨ (τ X0) = (M.op y y) ∨ (τ X0) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have i₁ := eq271927 X0
       have i₂ := eq1916 (τ X0) y y
       grind)
    | exact superpose eq1916 eq271927
    | (have j0 := eq271927 X0
       grind)
    | exact resolve eq271927 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916 eq271927
  have eq3601601 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq3947 eq272027
    | (have j0 := eq272027 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq272027 eq3947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947 eq272027
  have eq3602020 : (M.op (σ x) (σ y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq99914 eq3601601
    | exact resolve eq3601601 eq99914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99914 eq3601601
  have eq3602098 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq29076 eq3602020
    | exact resolve eq3602020 eq29076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29076 eq3602020
  have eq3602152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq28972 eq3602098
    | exact resolve eq3602098 eq28972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28972 eq3602098
  have eq3602184 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have r₁ := eq3602152
       have r₂ := eq28
       grind)
    | exact resolve eq3602152 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602152
  have eq3602210 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32582 eq3602184
    | exact resolve eq3602184 eq32582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602184
  have eq3602222 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3602210
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3602210
    | exact resolve eq3602210 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3602210
  have eq3603936 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (M.op y X0)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq612 y y x
       have i₂ := eq3602222
       grind)
    | exact superpose eq3602222 eq612
    | exact resolve eq612 eq3602222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq3602222
  have eq3604064 : ∀ X0 : G, (M.op x (M.op y X0)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq32582 eq3603936
    | exact resolve eq3603936 eq32582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32582 eq3603936
  have eq3604197 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3604064 x
       have i₂ := eq1301 x
       grind)
    | exact superpose eq1301 eq3604064
    | exact resolve eq3604064 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301 eq3604064
  have eq3604198 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq3604197
  have eq3604428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3604198 eq15
    | exact resolve eq15 eq3604198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3604198
  have eq3605650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq3604428
    | exact resolve eq3604428 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3604428
  have eq3605985 : False := by grind
  exact eq3605985

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation4111 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq9 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq106 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29
  have eq343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11940 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq343 x y
       grind)
    | exact superpose eq343 eq16
    | (have j1 := eq343 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq343 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq343 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq343 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq11977 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11940
  have eq12081 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq11977
       grind)
    | exact superpose eq11977 eq16
    | exact resolve eq16 eq11977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12083 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq11977
       grind)
    | exact superpose eq11977 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11977
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11977
       grind)
    | exact resolve eq13 eq11977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11977
  have eq12109 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq12083
  have eq12110 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq12109
  have eq12112 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12110
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12110
    | exact resolve eq12110 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12110
  have eq19704 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12112
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq12112
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq12112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19707 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq12112
       grind)
    | exact superpose eq12112 eq10
    | exact resolve eq10 eq12112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12112
  have eq19728 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq19704
  have eq19733 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19707
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq19707
    | exact resolve eq19707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19707
  have eq19734 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19728
       have r₂ := eq12081
       grind)
    | exact resolve eq19728 eq12081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12081 eq19728
  have eq19735 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq19733
       have r₂ := eq13 y x
       grind)
    | exact resolve eq19733 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19733
  have eq39420 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq33 x y
       have i₂ := eq19735
       grind)
    | exact superpose eq19735 eq33
    | (have j0 := eq33 x y
       grind)
    | exact resolve eq33 eq19735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq19735
  have eq39423 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq39420
  have eq58013 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq39423
       grind)
    | exact superpose eq39423 eq16
    | exact resolve eq16 eq39423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39423
  have eq76523 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq58013
       have i₂ := eq19734
       grind)
    | exact superpose eq19734 eq58013
    | exact resolve eq58013 eq19734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19734 eq58013
  have eq76524 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq76523
  have eq76525 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq76524
  have eq102485 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq76525
       grind)
    | exact superpose eq76525 eq10
    | exact resolve eq10 eq76525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76525
  have eq102512 : x = y ∨ x = y := by
    first
    | (have i₁ := eq102485
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102485
    | exact resolve eq102485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102485
  have eq102513 : x = y := by grind
  clear eq102512
  have eq114954 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102513
       grind)
    | exact superpose eq102513 eq16
    | exact resolve eq16 eq102513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102513
  have eq114955 : False := by grind
  exact eq114955
