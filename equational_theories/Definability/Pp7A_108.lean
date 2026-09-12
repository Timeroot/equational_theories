import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxy_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq34
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq63 : ∀ X0 : G, (M.op (τ (σ y)) (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 X0 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X2 ∨ (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op (M.op X0 X1) (M.op X2 X2))) ∨ (M.op X1 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq14 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) (k X2 X2)) X1) = X2 ∨ (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op (M.op X0 X1) (M.op X2 X2))) ∨ (M.op X1 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142 X0 X1 X2
       have i₂ := eq83 X2
       grind)
    | exact superpose eq83 eq142
    | (have j0 := eq142 X0 X1 X2
       grind)
    | exact resolve eq142 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq158 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq138
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq138
    | exact resolve eq138 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq160 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq136
    | exact resolve eq136 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq168 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = (k (M.op (M.op X0 X1) (M.op X2 X2)) (M.op (M.op X0 X1) (M.op X2 X2))) ∨ (k (M.op (M.op X0 X1) (k X2 X2)) X1) = X2 ∨ (M.op X1 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 X0 X1 X2
       have i₂ := eq83 (M.op (M.op X0 X1) (M.op X2 X2))
       grind)
    | exact superpose eq83 eq155
    | (have j0 := eq155 X0 X1 X2
       grind)
    | exact resolve eq155 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq171 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq158
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq158
    | exact resolve eq158 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq173 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq160
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq160
    | exact resolve eq160 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq181 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (k X2 X2))) = (k (M.op (M.op X0 X1) (k X2 X2)) (M.op (M.op X0 X1) (k X2 X2))) ∨ (k (M.op (M.op X0 X1) (k X2 X2)) X1) = X2 ∨ (M.op X1 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168 X0 X1 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq168
    | (have j0 := eq168 X0 X1 X2
       grind)
    | exact resolve eq168 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq190 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X2 ∨ (M.op X1 (M.op (M.op X0 X1) (k X2 X2))) = (k (M.op (M.op X0 X1) (k X2 X2)) (M.op (M.op X0 X1) (k X2 X2))) ∨ (k (M.op (M.op X0 X1) (k X2 X2)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq181
    | (have j0 := eq181 X0 X1 X2
       grind)
    | exact resolve eq181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq195 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (k X2 X2))) = (k (M.op (M.op X0 X1) (k X2 X2)) (M.op (M.op X0 X1) (k X2 X2))) ∨ (k X1 X1) = X2 ∨ (k (M.op (M.op X0 X1) (k X2 X2)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq190 X0 X1 X2
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq190
    | (have j0 := eq190 X0 X1 X2
       grind)
    | exact resolve eq190 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq225 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq63 (M.op sF2 sF2)
       have i₂ := eq9 sF2 sF2 sF2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq230
    | exact resolve eq230 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq236 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq225
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq225
    | exact resolve eq225 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq237 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (k X0 X0)) (M.op X0 (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq231
    | exact resolve eq231 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq250 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (M.op (τ (σ y)) (M.op (M.op x y) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq63
    | exact resolve eq63 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq252 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq83 (M.op X0 X0)
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq255 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq255
    | exact resolve eq255 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq257 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq252
    | (have j0 := eq252 X0 X1
       grind)
    | (have r₁ := eq252 X0 X0
       have r₂ := eq83 X0
       grind)
    | exact resolve eq252 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq258 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq250
    | exact resolve eq250 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq261 : (k (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq236 eq13
    | (have j0 := eq13 (M.op x y) (τ (σ y))
       grind)
    | exact resolve eq13 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq261
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq261 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq266 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq264
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq264
    | exact resolve eq264 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq267 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq266
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq266
    | exact resolve eq266 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq293 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq65
    | exact resolve eq65 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq340 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq237 eq9
    | exact resolve eq9 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (k X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq237 eq9
    | exact resolve eq9 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq351 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (k X0 X0)) (M.op X0 (k X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq350 X0 X1 X2
       have i₂ := eq83 X2
       grind)
    | exact superpose eq83 eq350
    | exact resolve eq350 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq399 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq66
    | exact resolve eq66 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (k X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq251 eq66
    | exact resolve eq66 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq438 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (M.op x y) (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq403 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq403
    | exact resolve eq403 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq441 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq399 X0
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq399
    | exact resolve eq399 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq454 : ∀ X0 : G, (M.op (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq438 eq9
    | exact resolve eq9 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq463 : ∀ X0 : G, (k (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq454 X0
       have i₂ := eq83 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq83 eq454
    | exact resolve eq454 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq467 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq463 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq463
    | exact resolve eq463 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq739 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq171
  have eq842 : ∀ X0 X1 X2 : G, (M.op X0 (k X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (k X0 X0)) X1 X2
       have i₂ := eq351 X0 X0 X0
       grind)
    | exact superpose eq351 eq9
    | exact resolve eq9 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : ∀ X0 X1 X2 : G, (k (k X0 X0) (k X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq842 X0 X1 X2
       have i₂ := eq441 X0
       grind)
    | exact superpose eq441 eq842
    | exact resolve eq842 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2531 : ∀ X0 X1 : G, (k (k (M.op X1 (k X0 X0)) (M.op X1 (k X0 X0))) (k (M.op X1 (k X0 X0)) (M.op X1 (k X0 X0)))) = (M.op (k X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq871 (M.op X1 (k X0 X0)) (k X1 X1) x
       have i₂ := eq351 X1 x X0
       grind)
    | exact superpose eq351 eq871
    | exact resolve eq871 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2566 : ∀ X0 X1 X2 : G, (M.op (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = (M.op (M.op (M.op X2 X1) X0) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X1 (M.op (M.op X2 X1) X0)
       have i₂ := eq871 X0 X1 X2
       grind)
    | exact superpose eq871 eq66
    | exact resolve eq66 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2590 : ∀ X0 X1 X2 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = (M.op (M.op (M.op X2 X1) X0) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2566 X0 X1 X2
       have i₂ := eq83 (k (k X0 X0) (k X0 X0))
       grind)
    | exact superpose eq83 eq2566
    | exact resolve eq2566 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq2566
  have eq2657 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) X0) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2590 X0 X1 X2
       have i₂ := eq467 X0
       grind)
    | exact superpose eq467 eq2590
    | exact resolve eq2590 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq3471 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k (k X1 X1) (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq293 eq2657
    | exact resolve eq2657 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq2657
  have eq3696 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X1 (k (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq351 (M.op X2 X0) X1 (k X0 X0)
       have i₂ := eq3471 X2 X0
       grind)
    | exact superpose eq3471 eq351
    | exact resolve eq351 eq3471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4953 : (k (M.op x y) (M.op x y)) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq236 eq253
    | (have j0 := eq253 (τ (σ y)) (M.op x y)
       grind)
    | exact resolve eq253 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq253
  have eq6213 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq257
    | (have j0 := eq257 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq257 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9749 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (k (M.op x y) (M.op x y))) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq42 eq3696
    | exact resolve eq3696 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9754 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k (k X0 X0) (k X0 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3696 X0 X1 (k (k X0 X0) (k X0 X0))
       have i₂ := eq340 X0
       grind)
    | exact superpose eq340 eq3696
    | exact resolve eq3696 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696
  have eq25392 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (k (k X0 X0) (k X0 X0)) (k X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq351 (k (k X0 X0) (k X0 X0)) X1 X2
       have i₂ := eq467 X0
       grind)
    | exact superpose eq467 eq351
    | exact resolve eq351 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq25476 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k (k (M.op (k X0 X0) (k (k X2 X2) (k X2 X2))) (M.op (k X0 X0) (k (k X2 X2) (k X2 X2)))) (k (M.op (k X0 X0) (k (k X2 X2) (k X2 X2))) (M.op (k X0 X0) (k (k X2 X2) (k X2 X2)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25392 X0 X1 X2
       have i₂ := eq2531 (k X2 X2) (k X0 X0)
       grind)
    | exact superpose eq2531 eq25392
    | exact resolve eq25392 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25392
  have eq25509 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k (k (k (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2))))) (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))))) (k (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2))))) (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2))))))) (k (k (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2))))) (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))))) (k (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2))))) (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2))))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25476 X1 X1 X2
       have i₂ := eq2531 (k (k X2 X2) (k X2 X2)) X1
       grind)
    | exact superpose eq2531 eq25476
    | exact resolve eq25476 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25476
  have eq25530 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25509 X0 X1 X2
       have i₂ := eq467 (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))))
       grind)
    | exact superpose eq467 eq25509
    | exact resolve eq25509 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25509
  have eq25542 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k (M.op X0 X2) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f25542_12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))) (M.op X0 (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2)))))) = X2 := by
      intro X0 X1 X2
      grind
    have f25542_13 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
      intro X0
      grind
    have f25542_22 : X2 ≠ (M.op (M.op X1 X0) (k (M.op X0 X2) (M.op X0 X2))) := by grind
    have f25542_23 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k (M.op X0 X2) (M.op X0 X2))) = X2 := by
      intro X0 X1 X2
      first
      | (have i₁ := f25542_12 X0 X1 X0
         have i₂ := f25542_13 X0
         grind)
      | exact superpose f25542_13 f25542_12
      | exact resolve f25542_12 f25542_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25542_52 : X2 ≠ X2 := by
      first
      | (have i₁ := f25542_22
         have i₂ := f25542_23 X0 X1 X2
         grind)
      | exact superpose f25542_23 f25542_22
      | (have r₁ := f25542_22
         have r₂ := f25542_23 X0 X1 X2
         grind)
      | exact resolve f25542_22 f25542_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25542_54 : False := by grind
    exact f25542_54
  clear eq25530
  have eq25675 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25542 X1 X1 (M.op (M.op X2 X1) X0)
       have i₂ := eq871 X0 X1 X2
       grind)
    | exact superpose eq871 eq25542
    | exact resolve eq25542 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq25687 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25542 X0 X1 (k X0 X0)
       have i₂ := eq441 X0
       grind)
    | exact superpose eq441 eq25542
    | exact resolve eq25542 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq25806 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X1 X0 (M.op X0 x)
       have i₂ := eq25542 X0 X1 x
       grind)
    | exact superpose eq25542 eq195
    | (have j0 := eq195 X0 X1 (M.op X1 X0)
       grind)
    | exact resolve eq195 eq25542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq26002 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25687 X0 X1
       have i₂ := eq467 X0
       grind)
    | exact superpose eq467 eq25687
    | exact resolve eq25687 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25687
  have eq26008 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25675 X0 X1 X2 X3
       have i₂ := eq467 X0
       grind)
    | exact superpose eq467 eq25675
    | exact resolve eq25675 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25675
  have eq27567 : (k (τ (σ y)) (τ (σ y))) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq42 eq26002
    | exact resolve eq26002 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26002
  have eq33620 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26008 X2 X1 X0 (k (k X0 X0) (k X0 X0))
       have i₂ := eq340 X0
       grind)
    | exact superpose eq340 eq26008
    | exact resolve eq26008 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq26008
  have eq34269 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (k (k (M.op X0 (k X2 X2)) (M.op X0 (k X2 X2))) (k (M.op X0 (k X2 X2)) (M.op X0 (k X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33620 X0 X1 X2
       have i₂ := eq2531 X2 X0
       grind)
    | exact superpose eq2531 eq33620
    | exact resolve eq33620 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33620
  have eq70915 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq173 eq6213
    | (have r₁ := eq6213
       have r₂ := eq173
       grind)
    | exact resolve eq6213 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq6213
  have eq70917 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq70915
  have eq70918 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by grind
  clear eq70917
  have eq70919 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq70918 eq15
    | exact resolve eq15 eq70918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70918
  have eq70930 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq70919
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq70919
    | exact resolve eq70919 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70919
  have eq70932 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq70930
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq70930
    | exact resolve eq70930 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70930
  have eq70933 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq70932
    | exact resolve eq70932 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70932
  have eq70947 : (τ (σ x)) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq70933 eq256
    | exact resolve eq256 eq70933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq71031 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq70933 eq15
    | exact resolve eq15 eq70933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70933
  have eq71064 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71031
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq71031
    | exact resolve eq71031 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71031
  have eq71141 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq71064
    | exact resolve eq71064 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71064
  have eq74005 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq70947 eq9749
    | exact resolve eq9749 eq70947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9749 eq70947
  have eq74159 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq74005
    | exact resolve eq74005 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq74005
  have eq74361 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq74159 eq15
    | exact resolve eq15 eq74159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74159
  have eq74391 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74361
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq74361
    | exact resolve eq74361 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74361
  have eq74473 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq74391
    | exact resolve eq74391 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74391
  have eq74906 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq74473 eq71141
    | exact resolve eq71141 eq74473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74908 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq74473
  have eq74910 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq74906
       have r₂ := eq74908
       grind)
    | exact resolve eq74906 eq74908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74906
  have eq77187 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq74910 eq74908
    | exact resolve eq74908 eq74910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74908
  have eq77277 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op X0 (k (k (σ x) (σ x)) (k (σ x) (σ x)))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq74910 eq9754
    | exact resolve eq9754 eq74910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9754 eq74910
  have eq77312 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq77187
  have eq77330 : (k (σ x) (σ x)) = (k (k (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ y) (σ y))) (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ y) (σ y)))) (k (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ y) (σ y))) (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77277 x
       have i₂ := eq34269 (k (k sF4 sF4) (k sF4 sF4)) x sF5
       grind)
    | exact superpose eq34269 eq77277
    | exact resolve eq77277 eq34269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34269 eq77277
  have eq77421 : (k (σ x) (σ x)) = (k (k (k (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))))) (k (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y))))))) (k (k (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))))) (k (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77330
       have i₂ := eq2531 (k sF5 sF5) (k sF4 sF4)
       grind)
    | exact superpose eq2531 eq77330
    | exact resolve eq77330 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77330
  have eq77497 : (k (σ x) (σ x)) = (k (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (M.op (k (σ x) (σ x)) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77421
       have i₂ := eq467 (k (M.op (k sF4 sF4) (k (k sF5 sF5) (k sF5 sF5))) (M.op (k sF4 sF4) (k (k sF5 sF5) (k sF5 sF5))))
       grind)
    | exact superpose eq467 eq77421
    | exact resolve eq77421 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77421
  have eq77548 : (k (σ x) (σ x)) = (k (k (k (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))))) (k (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y))))))) (k (k (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))))) (k (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77497
       have i₂ := eq2531 (k (k sF5 sF5) (k sF5 sF5)) sF4
       grind)
    | exact superpose eq2531 eq77497
    | exact resolve eq77497 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531 eq77497
  have eq77579 : (k (σ x) (σ x)) = (M.op (σ x) (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77548
       have i₂ := eq467 (M.op sF4 (k (k (k sF5 sF5) (k sF5 sF5)) (k (k sF5 sF5) (k sF5 sF5))))
       grind)
    | exact superpose eq467 eq77548
    | exact resolve eq77548 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77548
  have eq77600 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77579
       have i₂ := eq467 sF5
       grind)
    | exact superpose eq467 eq77579
    | exact resolve eq77579 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq77579
  have eq77611 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq77600
    | exact resolve eq77600 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77600
  have eq78141 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq77611 eq33
    | exact resolve eq33 eq77611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77611
  have eq78223 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq78141
       have r₂ := eq71141
       grind)
    | exact resolve eq78141 eq71141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71141 eq78141
  have eq124309 : (k (M.op x y) (M.op x y)) ≠ (k (M.op x y) (M.op x y)) ∨ (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq267 eq4953
    | (have r₁ := eq4953
       have r₂ := eq267
       grind)
    | exact resolve eq4953 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953
  have eq124310 : (k (M.op x y) (τ (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) := by grind
  clear eq124309
  have eq124311 : (k (M.op x y) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq27567 eq124310
    | exact resolve eq124310 eq27567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27567 eq124310
  have eq125862 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq124311 eq267
    | exact resolve eq267 eq124311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq124311
  have eq126030 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) := by grind
  clear eq125862
  have eq128398 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (τ (σ y)))) := by
    first
    | exact superpose eq126030 eq15
    | exact resolve eq15 eq126030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126030
  have eq128413 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq128398
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq128398
    | exact resolve eq128398 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq128398
  have eq128414 : (k (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq26 eq128413
    | exact resolve eq128413 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128413
  have eq128415 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq128414
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq128414
    | exact resolve eq128414 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128414
  have eq128416 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq128415
    | exact resolve eq128415 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq128415
  have eq128417 : (k (k (σ y) (σ x)) (k (σ y) (σ x))) = (k (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq78223 eq128416
    | exact resolve eq128416 eq78223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128416
  have eq132036 : (k (σ (k (σ y) (σ x))) (σ (k (σ y) (σ x)))) = (σ (k (k (σ y) (σ x)) (σ y))) := by
    first
    | exact superpose eq128417 eq15
    | exact resolve eq15 eq128417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128417
  have eq132080 : (k (σ (k (σ y) (σ x))) (σ (k (σ y) (σ x)))) = (k (σ (k (σ y) (σ x))) (σ (σ y))) := by
    first
    | (have i₁ := eq132036
       have i₂ := eq15 (k sF5 sF4) sF5
       grind)
    | exact superpose eq15 eq132036
    | exact resolve eq132036 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132036
  have eq132177 : (k (k (σ (σ y)) (σ (σ x))) (k (σ (σ y)) (σ (σ x)))) = (k (k (σ (σ y)) (σ (σ x))) (σ (σ y))) := by
    first
    | (have i₁ := eq132080
       have i₂ := eq15 sF5 sF4
       grind)
    | exact superpose eq15 eq132080
    | exact resolve eq132080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132080
  have eq292420 : ∀ X0 : G, (M.op (k (σ (σ y)) (σ (σ x))) (M.op (k (k (σ (σ y)) (σ (σ x))) (σ (σ y))) (k X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq132177 eq258
    | exact resolve eq258 eq132177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq132177
  have eq318938 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k (k X0 X0) (k X0 X0))) = X2 ∨ (k X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25542 X1 X1 X0
       have i₂ := eq25806 X0 X1
       grind)
    | exact superpose eq25806 eq25542
    | (have j1 := eq25806 X2 X0
       grind)
    | exact resolve eq25542 eq25806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25542 eq25806
  have eq319729 : ∀ X0 X2 : G, (k X2 X2) = (M.op X0 X2) ∨ X0 = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq318938 X0 x X2
       have i₂ := eq3471 x X0
       grind)
    | exact superpose eq3471 eq318938
    | (have j0 := eq318938 X0 x X2
       grind)
    | exact resolve eq318938 eq3471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471 eq318938
  have eq320309 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq257 x X0
       have i₂ := eq319729 X0 x
       grind)
    | exact superpose eq319729 eq257
    | (have j0 := eq257 X0 X1
       have j1 := eq319729 (k X0 X0) (k X1 X1)
       grind)
    | (have r₁ := eq257 x X0
       have r₂ := eq319729 X0 x
       grind)
    | (have r₁ := eq257 X0 X1
       have r₂ := eq319729 (M.op X1 X0) (k X0 X0)
       grind)
    | (have r₁ := eq257 X0 X1
       have r₂ := eq319729 (k X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq257 eq319729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq320825 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq319729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319729
  have eq320828 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq320309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320309
  have eq321147 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq320828 X0 X1
       have j1 := eq320825 (k X0 X0) (k X1 X1)
       grind)
    | (have r₁ := eq320828 X0 X0
       have r₂ := eq320825 X0 X0
       grind)
    | (have r₁ := eq320828 X1 X0
       have r₂ := eq320825 X0 X1
       grind)
    | (have r₁ := eq320828 (k X1 X1) (k X1 X0)
       have r₂ := eq320825 X0 X1
       grind)
    | exact resolve eq320828 eq320825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320825 eq320828
  have eq324532 : ∀ X0 X1 : G, (M.op (k (σ (σ y)) (σ (σ x))) (M.op (k (k (σ (σ y)) (σ (σ x))) (σ (σ y))) (k X0 X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq292420 X1
       have i₂ := eq321147 X0 X1
       grind)
    | (have i₁ := eq292420 X0
       have i₂ := eq321147 X0 X1
       grind)
    | exact superpose eq321147 eq292420
    | (have j1 := eq321147 X0 X1
       grind)
    | exact resolve eq292420 eq321147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321147
  have eq325408 : ∀ X0 X1 : G, X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | exact superpose eq292420 eq324532
    | (have j0 := eq324532 X0 X1
       grind)
    | exact resolve eq324532 eq292420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292420 eq324532
  have eq325409 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq325408 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325408
  have eq327926 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32
       have i₂ := eq325409 sF5 sF4
       grind)
    | exact superpose eq325409 eq32
    | (have j1 := eq325409 (σ y) (σ x)
       grind)
    | exact resolve eq32 eq325409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq325409
  have eq328740 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq327926 eq33
    | exact resolve eq33 eq327926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327926
  have eq328906 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq328740
       have r₂ := eq78223
       grind)
    | exact resolve eq328740 eq78223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78223 eq328740
  have eq329097 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq328906 eq739
    | exact resolve eq739 eq328906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq329274 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq328906 eq77312
    | exact resolve eq77312 eq328906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77312 eq328906
  have eq329359 : (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq329274
  have eq329366 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq329097
  have eq329367 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq329366
  have eq329655 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq329367 eq33
    | exact resolve eq33 eq329367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq329367
  have eq329850 : False := by grind
  exact eq329850

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq102 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq106 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq102
    | exact resolve eq102 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq106
    | exact resolve eq106 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq106
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq78 y x
       grind)
    | exact superpose eq78 eq101
    | (have j1 := eq78 y x
       grind)
    | exact resolve eq101 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq136 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq108
       grind)
    | exact superpose eq108 eq16
    | exact resolve eq16 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq509 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq602 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq941 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117 eq78
    | (have j0 := eq78 (σ y) (σ x)
       grind)
    | exact resolve eq78 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq117
  have eq942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq941
    | exact resolve eq941 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq945 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq942
       have r₂ := eq28
       grind)
    | exact resolve eq942 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq947 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq945 eq136
    | exact resolve eq136 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq945
  have eq966 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq947
    | exact resolve eq947 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq947
  have eq967 : x = (M.op y y) := by grind
  clear eq966
  have eq1082 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq967
       grind)
    | exact superpose eq967 eq108
    | exact resolve eq108 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1088 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1
       have i₂ := eq967
       grind)
    | exact superpose eq967 eq14
    | exact resolve eq14 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1101 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1082
    | exact resolve eq1082 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1108 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq1101 eq14
    | exact resolve eq14 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1535 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq499 eq1088
    | exact resolve eq1088 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq1088
  have eq1545 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq1535
       have i₂ := eq54 x x
       grind)
    | exact superpose eq54 eq1535
    | exact resolve eq1535 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1561 : x = (M.op x y) := by
    first
    | (have i₁ := eq509 x
       have i₂ := eq1545
       grind)
    | exact superpose eq1545 eq509
    | exact resolve eq509 eq1545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1571 : x = (M.op x y) := by
    first
    | (have i₁ := eq1561
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1561
    | exact resolve eq1561 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1561
  have eq1607 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1571 eq21
    | exact resolve eq21 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1571
  have eq1640 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1607
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1607
    | exact resolve eq1607 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1607
  have eq1644 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1640 eq27
    | exact resolve eq27 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2582 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1640 eq1108
    | exact resolve eq1108 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq1640
  have eq2739 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2582 (M.op sF1 sF1) x
       have i₂ := eq602 sF1 x
       grind)
    | exact superpose eq602 eq2582
    | exact resolve eq2582 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq2582
  have eq2756 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2739
       have i₂ := eq54 sF1 sF1
       grind)
    | exact superpose eq54 eq2739
    | exact resolve eq2739 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2739
  have eq2794 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2756 eq509
    | exact resolve eq509 eq2756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq2756
  have eq2816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1644 eq2794
    | exact resolve eq2794 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644 eq2794
  have eq2820 : False := by grind
  exact eq2820

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq52 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq52
    | exact resolve eq52 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq85 (σ X0)
       grind)
    | exact superpose eq85 eq15
    | exact resolve eq15 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq85 (τ X0)
       grind)
    | exact superpose eq85 eq18
    | exact resolve eq18 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq95
    | exact resolve eq95 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq102
    | exact resolve eq102 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq102
  have eq118 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq189 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq198 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq251 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq166 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq70 X1 X1
       grind)
    | exact superpose eq70 eq166
    | exact resolve eq166 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq166
  have eq311 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq51 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq51 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq9
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq357 X0 X1 X2 X3
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq357
    | exact resolve eq357 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq413 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq311 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq311 X0 X0 X0
       grind)
    | exact superpose eq311 eq311
    | exact resolve eq311 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq311 X0 X0 X0
       grind)
    | exact superpose eq311 eq9
    | exact resolve eq9 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq489 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (M.op (σ (σ (M.op X0 X0))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq118
    | exact resolve eq118 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq640 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251 X2 X3
       have i₂ := eq441 X2 X0 X1
       grind)
    | exact superpose eq441 eq251
    | exact resolve eq251 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X2
       have i₂ := eq441 X2 X0 X1
       grind)
    | exact superpose eq441 eq65
    | exact resolve eq65 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq844 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq198 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq198 X0 X1
       grind)
    | exact superpose eq198 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq198 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq198 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq198 X0 X1
       grind)
    | exact resolve eq13 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq868 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq844 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq880 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq868 X0 X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq868
    | (have j0 := eq868 X0 X1
       grind)
    | exact resolve eq868 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq881 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq880 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq893 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq881 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq881
    | (have j0 := eq881 X0 X1
       grind)
    | exact resolve eq881 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq894 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq893 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq2162 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq67 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq67 eq67
    | exact resolve eq67 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3573 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq372 (M.op X4 (M.op X3 X2)) (M.op X0 X1) X2 X3
       have i₂ := eq372 X0 X1 (M.op X3 X2) X4
       grind)
    | exact superpose eq372 eq372
    | exact resolve eq372 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3697 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X3 X2 X3 X2
       have i₂ := eq372 X2 X3 X0 X1
       grind)
    | exact superpose eq372 eq67
    | exact resolve eq67 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq4124 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq894 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq894
    | exact resolve eq894 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4148 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq894 x y
       grind)
    | exact superpose eq894 eq16
    | (have j1 := eq894 x y
       grind)
    | exact resolve eq16 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq4263 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4124 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4124
    | (have j0 := eq4124 X0 X1
       grind)
    | exact resolve eq4124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4124
  have eq4278 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4263 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq4263
    | (have j0 := eq4263 X0 X1
       grind)
    | exact resolve eq4263 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq4263
  have eq9070 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq413 (M.op X0 (M.op X0 X0)) X1 (M.op X2 X0)
       have i₂ := eq251 X0 X2
       grind)
    | exact superpose eq251 eq413
    | exact resolve eq413 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9516 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9070 X0 X1 X2
       have i₂ := eq52 X2 X0
       grind)
    | exact superpose eq52 eq9070
    | exact resolve eq9070 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9070
  have eq9656 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9516 X0 X1 X2
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq9516
    | exact resolve eq9516 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9516
  have eq9717 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9656 X0 X1 X2
       have i₂ := eq251 X0 X0
       grind)
    | exact superpose eq251 eq9656
    | exact resolve eq9656 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9656
  have eq9746 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9717 X0 X1 X2
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9717
    | exact resolve eq9717 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq9717
  have eq9814 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9746 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq413 X0 x X1
       grind)
    | exact superpose eq413 eq9746
    | exact resolve eq9746 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9746
  have eq10037 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9814 X0 X1 X2
       have i₂ := eq251 X0 X1
       grind)
    | exact superpose eq251 eq9814
    | exact resolve eq9814 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9814
  have eq10099 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10037 X0 X1 X2
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq10037
    | exact resolve eq10037 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10037
  have eq12999 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3697 (M.op X1 X1) (M.op x x) X1 (M.op X0 X0)
       have i₂ := eq51 X1 x x X0
       grind)
    | exact superpose eq51 eq3697
    | exact resolve eq3697 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq13012 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3697 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq3697
    | exact resolve eq3697 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq13166 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13012 X0 X1 X2 X3
       have i₂ := eq10099 X0 X3 X0
       grind)
    | exact superpose eq10099 eq13012
    | exact resolve eq13012 eq10099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13012
  have eq13176 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12999 X0 X1
       have i₂ := eq10099 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq10099 eq12999
    | exact resolve eq12999 eq10099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10099 eq12999
  have eq13618 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13176 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq413 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq413 eq13176
    | exact resolve eq13176 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq13637 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op (M.op X2 (M.op X1 X1)) X0))) = (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13176 (M.op (M.op X2 (M.op X1 X1)) X0) X1
       have i₂ := eq441 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq441 eq13176
    | exact resolve eq13176 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13931 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op (M.op X2 (M.op X1 X1)) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13637 X0 X1 X2
       have i₂ := eq251 X0 (M.op X2 (M.op X1 X1))
       grind)
    | exact superpose eq251 eq13637
    | exact resolve eq13637 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13637
  have eq13949 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13618 X0 X1
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq13618
    | exact resolve eq13618 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13618
  have eq14019 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X1 X1)) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13931 X0 X1 X2
       have i₂ := eq52 (M.op X2 (M.op X1 X1)) X0
       grind)
    | exact superpose eq52 eq13931
    | exact resolve eq13931 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13931
  have eq14036 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13949 X0 X1
       have i₂ := eq251 X0 X1
       grind)
    | exact superpose eq251 eq13949
    | exact resolve eq13949 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq13949
  have eq14433 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14036 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq640 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq640 eq14036
    | exact resolve eq14036 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq14036
  have eq15164 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13176 X2 X1
       have i₂ := eq14433 X2 X1 X0
       grind)
    | (have i₁ := eq13176 X0 X1
       have i₂ := eq14433 X0 X1 X1
       grind)
    | exact superpose eq14433 eq13176
    | exact resolve eq13176 eq14433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13176
  have eq36357 : ∀ X0 X1 : G, (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ (M.op X0 X0)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq489 (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq489
    | exact resolve eq489 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq48591 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14019 (M.op X0 X0) X1 x
       have i₂ := eq13166 X0 x X1 X1
       grind)
    | exact superpose eq13166 eq14019
    | exact resolve eq14019 eq13166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13166 eq14019
  have eq55213 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4278 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4278
    | exact resolve eq4278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq85063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4148
       have i₂ := eq55213 y x
       grind)
    | exact superpose eq55213 eq4148
    | (have j1 := eq55213 y x
       grind)
    | exact resolve eq4148 eq55213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148
  have eq85066 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq85063
  have eq95620 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48591 X1 X2
       have i₂ := eq14433 (M.op X1 (M.op X2 X1)) X1 X0
       grind)
    | (have i₁ := eq48591 X1 X1
       have i₂ := eq14433 (M.op X1 (M.op X1 X1)) X1 X1
       grind)
    | exact superpose eq14433 eq48591
    | exact resolve eq48591 eq14433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14433 eq48591
  have eq169142 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95620 X2 X3 X2
       have i₂ := eq372 X2 X3 X0 X1
       grind)
    | exact superpose eq372 eq95620
    | exact resolve eq95620 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq95620
  have eq375925 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3573 X0 X1 X2 X3 X4
       have i₂ := eq15164 X0 X1 (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1))
       grind)
    | exact superpose eq15164 eq3573
    | exact resolve eq3573 eq15164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3573
  have eq375926 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq375925 X0 X1 X2 X3 X4
       have i₂ := eq52 (M.op X4 (M.op X3 X2)) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq375925
    | exact resolve eq375925 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375925
  have eq375927 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq375926 X0 X1 X2 X3 x
       have i₂ := eq15164 x (M.op X3 X2) (M.op X0 X1)
       grind)
    | exact superpose eq15164 eq375926
    | exact resolve eq375926 eq15164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15164 eq375926
  have eq375928 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X3 X2) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq375927 X0 X1 X2 X3
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq375927
    | exact resolve eq375927 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq375927
  have eq375929 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X3 X2) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq375928 X0 X1 X2 X3
       have i₂ := eq2162 X1 X0 X1
       grind)
    | exact superpose eq2162 eq375928
    | exact resolve eq375928 eq2162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162 eq375928
  have eq376507 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) = (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq375929 X0 X0 X2 X3
       have i₂ := eq441 X0 X1 X2
       grind)
    | exact superpose eq441 eq375929
    | exact resolve eq375929 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq375929
  have eq378117 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X2 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq376507 X0 X1 X2 X3 X4
       have i₂ := eq644 X0 X1 X2
       grind)
    | exact superpose eq644 eq376507
    | exact resolve eq376507 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq376507
  have eq1137485 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85066
       grind)
    | exact superpose eq85066 eq16
    | exact resolve eq16 eq85066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137486 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq119 x (σ y)
       have i₂ := eq85066
       grind)
    | exact superpose eq85066 eq119
    | (have j0 := eq119 x (σ y)
       grind)
    | (have r₁ := eq119 x (σ y)
       have r₂ := eq85066
       grind)
    | exact resolve eq119 eq85066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1137804 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (M.op X1 X0) (σ (M.op x x))))) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq169142 X0 X1 (σ x) (σ y)
       have i₂ := eq85066
       grind)
    | exact superpose eq85066 eq169142
    | exact resolve eq169142 eq85066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85066 eq169142
  have eq1137941 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1137486
  have eq1137983 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1137804 x x
       have i₂ := eq123 x x x
       grind)
    | exact superpose eq123 eq1137804
    | exact resolve eq1137804 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1137804
  have eq1138102 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1137941
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1137941
    | exact resolve eq1137941 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137941
  have eq1138122 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1137983
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq1137983
    | exact resolve eq1137983 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137983
  have eq1138179 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1138102
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq1138102
    | exact resolve eq1138102 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138102
  have eq1138194 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1138122
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq1138122
    | exact resolve eq1138122 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138122
  have eq1141138 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1138179
       have i₂ := eq55213 y x
       grind)
    | exact superpose eq55213 eq1138179
    | (have j1 := eq55213 y x
       grind)
    | exact resolve eq1138179 eq55213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55213 eq1138179
  have eq1141435 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1141138
  have eq1149435 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1141435
       have i₂ := eq1138194
       grind)
    | exact superpose eq1138194 eq1141435
    | exact resolve eq1141435 eq1138194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138194 eq1141435
  have eq1149823 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1149435
  have eq1150056 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1149823
       have r₂ := eq1137485
       grind)
    | exact resolve eq1149823 eq1137485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137485 eq1149823
  have eq1150550 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op X0 (M.op (M.op x x) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq378117 X1 X2 X0 y x
       have i₂ := eq1150056
       grind)
    | exact superpose eq1150056 eq378117
    | exact resolve eq378117 eq1150056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150626 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1150550 X0 x x
       have i₂ := eq378117 x x X0 x x
       grind)
    | exact superpose eq378117 eq1150550
    | exact resolve eq1150550 eq378117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378117 eq1150550
  have eq1151252 : ∀ X0 : G, y = (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ (M.op X0 X0)))) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq36357 X0 y
       have i₂ := eq1150626 y
       grind)
    | exact superpose eq1150626 eq36357
    | exact resolve eq36357 eq1150626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150626
  have eq1153053 : ∀ X0 : G, y = (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ (M.op X0 X0)))) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq1151252 X0
       have i₂ := eq1150056
       grind)
    | exact superpose eq1150056 eq1151252
    | exact resolve eq1151252 eq1150056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150056 eq1151252
  have eq1153776 : x = y := by
    first
    | (have i₁ := eq1153053 x
       have i₂ := eq36357 x x
       grind)
    | exact superpose eq36357 eq1153053
    | exact resolve eq1153053 eq36357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36357 eq1153053
  have eq1154979 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1153776
       grind)
    | exact superpose eq1153776 eq16
    | exact resolve eq16 eq1153776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153776
  have eq1154982 : False := by grind
  exact eq1154982

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq52 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 y x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq55 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ y) (σ x)
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
  clear eq30
  have eq76 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq52 (M.op sF0 sF0)
       have i₂ := eq9 sF0 sF0 sF0
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y x) := by
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
  have eq95 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq58 eq95
    | exact resolve eq95 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq116 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq101 (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq116
    | exact resolve eq116 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq116
  have eq368 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq378 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq58
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq383 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq378
    | exact resolve eq378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq386 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq383
    | exact resolve eq383 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq388 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq26 eq386
    | exact resolve eq386 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq516 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
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
  have eq584 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq53 X1 x x X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq591 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
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
  have eq594 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq55
  have eq601 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq594
    | exact resolve eq594 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq602 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq593
    | exact resolve eq593 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq604 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq591 X0 X1 X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq591
    | exact resolve eq591 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq621 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq601 X0 X1
       grind)
    | exact superpose eq601 eq602
    | exact resolve eq602 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq623 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq604 X0 X1 X2 X3
       have i₂ := eq601 X0 X1
       grind)
    | exact superpose eq601 eq604
    | exact resolve eq604 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq604
  have eq641 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq621 eq623
    | exact resolve eq623 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq1073 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op (M.op X1 X0) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq584 (M.op X1 X0) X2 X3
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq584
    | exact resolve eq584 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq584 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq584 X0 X0 X0
       grind)
    | exact superpose eq584 eq584
    | exact resolve eq584 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq584 X0 X0 X0
       grind)
    | exact superpose eq584 eq52
    | exact resolve eq52 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq588 (M.op x (M.op x x)) x
       have i₂ := eq584 x x x
       grind)
    | exact superpose eq584 eq588
    | exact resolve eq588 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1134 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq516 X0 X0
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq516
    | exact resolve eq516 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1 X0
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq584
    | exact resolve eq584 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 X1 : G, (M.op (M.op y (M.op (M.op x y) X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X0 X1
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq584
    | exact resolve eq584 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq588 X0 X0
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq588
    | exact resolve eq588 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1139 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) X0)) (M.op y (M.op (M.op x y) X0))) = (M.op (M.op X0 X0) (M.op y (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq54 X0 (M.op X0 X0)
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq54
    | exact resolve eq54 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1141 : (M.op x y) = (M.op y (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq52 sF0
       have i₂ := eq1097 sF0
       grind)
    | exact superpose eq1097 eq52
    | exact resolve eq52 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq76 eq1141
    | exact resolve eq1141 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1150 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op y (M.op (M.op x y) X0))) = (M.op (M.op (M.op x y) X0) (M.op y (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq1139 X0
       have i₂ := eq54 y (M.op sF0 X0)
       grind)
    | exact superpose eq54 eq1139
    | exact resolve eq1139 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1151 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq1134 (M.op X0 X1)
       grind)
    | exact superpose eq1134 eq54
    | exact resolve eq54 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1152 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq1134 (σ X0)
       grind)
    | exact superpose eq1134 eq117
    | exact resolve eq117 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ X0))))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq1134 (σ X0)
       grind)
    | exact superpose eq1134 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq1211 : (M.op (σ x) (σ y)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq388
       have i₂ := eq1134 sF2
       grind)
    | exact superpose eq1134 eq388
    | exact resolve eq388 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq1214 : (M.op (σ x) (σ y)) ≠ (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ x))))) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq1134 sF2
       grind)
    | exact superpose eq1134 eq108
    | exact resolve eq108 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1273 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op y (M.op (M.op x y) X0))) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))))) := by
    intro X0
    first
    | (have i₁ := eq1150 X0
       have i₂ := eq1151 y (M.op sF0 X0)
       grind)
    | exact superpose eq1151 eq1150
    | exact resolve eq1150 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1444 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1101 X0 X1
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq1101
    | exact resolve eq1101 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1462 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))))) = X0 := by
    intro X0
    first
    | exact superpose eq1444 eq1273
    | exact resolve eq1273 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1799 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ X0))))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq1162
    | (have j0 := eq1162 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq1162 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1975 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) X0) := by
    intro X0 X1
    first
    | exact superpose eq52 eq1135
    | exact resolve eq1135 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2018 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X0)))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1975 X0 X1
       have i₂ := eq1134 (M.op X0 X0)
       grind)
    | exact superpose eq1134 eq1975
    | exact resolve eq1975 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq2038 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op y (M.op (M.op x y) X0))) X0) := by
    intro X0 X1
    first
    | exact superpose eq52 eq2018
    | exact resolve eq2018 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq6097 : (M.op y (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq621 sF4 sF4
       have i₂ := eq1097 sF4
       grind)
    | exact superpose eq1097 eq621
    | exact resolve eq621 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq6111 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq52 eq6097
    | exact resolve eq6097 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6097
  have eq6216 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1152 X0
       grind)
    | exact superpose eq1152 eq10
    | exact resolve eq10 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6348 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1074 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1074
    | (have j0 := eq1074 y x X0
       grind)
    | exact resolve eq1074 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6361 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq1074
    | (have j0 := eq1074 (σ y) (σ x) X0
       grind)
    | exact resolve eq1074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6375 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op y (M.op (M.op x y) X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1074 X0 X1 X2
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq1074
    | exact resolve eq1074 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6379 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op (M.op X2 (M.op X2 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1074 X2 X1 (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0))
       have i₂ := eq1074 (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0
       grind)
    | exact superpose eq1074 eq1074
    | exact resolve eq1074 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6400 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq584 X2 X1 (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0))
       have i₂ := eq1074 (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0
       grind)
    | exact superpose eq1074 eq584
    | exact resolve eq584 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq6408 : ∀ X0 X1 : G, (M.op (M.op y (M.op (M.op x y) X1)) (M.op X1 X0)) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1136 X1 (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0))
       have i₂ := eq1074 (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0
       grind)
    | exact superpose eq1074 eq1136
    | exact resolve eq1136 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq1136
  have eq6432 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op y (M.op (M.op x y) X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6408 X0 X1
       have i₂ := eq588 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq588 eq6408
    | exact resolve eq6408 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6408
  have eq6440 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6400 X0 X1 X2
       have i₂ := eq588 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq588 eq6400
    | exact resolve eq6400 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6400
  have eq6455 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op (M.op X2 (M.op X2 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6379 X0 X1 X2
       have i₂ := eq588 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq588 eq6379
    | exact resolve eq6379 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq6379
  have eq6471 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op y (M.op (M.op x y) (σ y))) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq6361 X0
       have i₂ := eq1097 sF3
       grind)
    | exact superpose eq1097 eq6361
    | exact resolve eq6361 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6361
  have eq6505 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X0))))) = (M.op (M.op y (M.op (M.op x y) X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6432 X0 X1
       have i₂ := eq1134 (M.op X0 X0)
       grind)
    | exact superpose eq1134 eq6432
    | exact resolve eq6432 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6432
  have eq6513 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6440 X0 X1 X2
       have i₂ := eq1134 (M.op X0 X0)
       grind)
    | exact superpose eq1134 eq6440
    | exact resolve eq6440 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6440
  have eq6525 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X0))))) = (M.op (M.op X1 X2) (M.op (M.op X2 (M.op X2 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6455 X0 X1 X2
       have i₂ := eq1134 (M.op X0 X0)
       grind)
    | exact superpose eq1134 eq6455
    | exact resolve eq6455 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6455
  have eq6540 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op y (M.op (M.op x y) X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq6505
    | exact resolve eq6505 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6505
  have eq6545 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq6513
    | exact resolve eq6513 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6513
  have eq6557 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op X1 X2) (M.op (M.op X2 (M.op X2 X2)) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq6525
    | exact resolve eq6525 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6525
  have eq6717 : ∀ X0 X1 : G, (M.op (M.op y (M.op y y)) (M.op X0 X0)) = (M.op (M.op X1 (M.op (M.op (M.op y (M.op y y)) (M.op X0 X0)) (M.op (M.op y (M.op y y)) (M.op X0 X0)))) (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq6348 eq1135
    | exact resolve eq1135 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6736 : ∀ X0 X1 : G, (M.op (M.op y (M.op y y)) (M.op X0 X0)) = (M.op (M.op X1 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))))))) (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6717 X0 X1
       have i₂ := eq1134 (M.op (M.op y (M.op y y)) (M.op X0 X0))
       grind)
    | exact superpose eq1134 eq6717
    | exact resolve eq6717 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6717
  have eq6750 : ∀ X0 X1 : G, (M.op (M.op y (M.op y y)) (M.op X0 X0)) = (M.op (M.op X1 (M.op y (M.op (M.op x y) (M.op y X0)))) (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq6348 eq6736
    | exact resolve eq6736 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348 eq6736
  have eq6760 : ∀ X0 : G, (M.op (M.op y (M.op y y)) (M.op X0 X0)) = (M.op (M.op y X0) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq2038 eq6750
    | exact resolve eq6750 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6750
  have eq6763 : ∀ X0 : G, (M.op (M.op y (M.op y y)) (M.op X0 X0)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))) := by
    intro X0
    first
    | (have i₁ := eq6760 X0
       have i₂ := eq1134 (M.op y X0)
       grind)
    | exact superpose eq1134 eq6760
    | exact resolve eq6760 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6760
  have eq6835 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq641
    | exact resolve eq641 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq7031 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op y (M.op (M.op x y) X0))) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6835 (M.op (M.op X1 (M.op X2 X3)) X0) X3 X2
       have i₂ := eq6835 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq6835 eq6835
    | exact resolve eq6835 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7049 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) X0)) = (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1151 (M.op x sF0) X0
       have i₂ := eq6835 X0 sF0 x
       grind)
    | exact superpose eq6835 eq1151
    | exact resolve eq1151 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq7052 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op x y)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op x y)) X0) (M.op (M.op X2 (M.op x y)) X0))) (M.op y (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1135 (M.op (M.op X2 sF0) X0) X1
       have i₂ := eq6835 X0 sF0 X2
       grind)
    | exact superpose eq6835 eq1135
    | exact resolve eq1135 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq7059 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op x y)) X0) = (M.op (M.op X1 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op x y)) X0)))))) (M.op y (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7052 X0 X1 X2
       have i₂ := eq1134 (M.op (M.op X2 sF0) X0)
       grind)
    | exact superpose eq1134 eq7052
    | exact resolve eq7052 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7052
  have eq7081 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op x y)) X0) = (M.op (M.op X1 (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X0)))))) (M.op y (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7059 X0 X1 X2
       have i₂ := eq6835 X0 sF0 X2
       grind)
    | exact superpose eq6835 eq7059
    | exact resolve eq7059 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7059
  have eq7087 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op x y)) X0) = (M.op (M.op y (M.op y (M.op (M.op x y) X0))) (M.op y (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X2
    first
    | exact superpose eq2038 eq7081
    | exact resolve eq7081 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038 eq7081
  have eq7090 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op x y)) X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X0))))))) := by
    intro X0 X2
    first
    | (have i₁ := eq7087 X0 X2
       have i₂ := eq1134 (M.op y (M.op y (M.op sF0 X0)))
       grind)
    | exact superpose eq1134 eq7087
    | exact resolve eq7087 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7087
  have eq7095 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X0))))) = (M.op X0 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X0)))))))) := by
    intro X0
    first
    | exact superpose eq7090 eq7049
    | exact resolve eq7049 eq7090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7049 eq7090
  have eq7529 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (τ (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ X0)))))))))) := by
    intro X0
    first
    | (have i₁ := eq6216 (M.op X0 X0)
       have i₂ := eq1152 X0
       grind)
    | exact superpose eq1152 eq6216
    | exact resolve eq6216 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6216
  have eq7642 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (τ (M.op y (M.op (M.op x y) (σ X0)))) := by
    intro X0
    first
    | exact superpose eq1462 eq7529
    | exact resolve eq7529 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7529
  have eq7680 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X0))))) = (τ (M.op y (M.op (M.op x y) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq7642 X0
       have i₂ := eq1134 (M.op X0 X0)
       grind)
    | exact superpose eq1134 eq7642
    | exact resolve eq7642 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7642
  have eq7713 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (τ (M.op y (M.op (M.op x y) (σ X0)))) := by
    intro X0
    first
    | exact superpose eq52 eq7680
    | exact resolve eq7680 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7680
  have eq7737 : ∀ X0 : G, (M.op y (M.op (M.op x y) (τ X0))) = (τ (M.op y (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq7713 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7713
    | exact resolve eq7713 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7713
  have eq10651 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))))))) := by
    intro X0
    first
    | exact superpose eq1462 eq1444
    | exact resolve eq1444 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444
  have eq10793 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (M.op X0 X0))) (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op y (M.op (M.op x y) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq6375 eq6471
    | exact resolve eq6471 eq6375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6375 eq6471
  have eq10821 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op y (M.op (M.op x y) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq1137 eq10793
    | exact resolve eq10793 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq10793
  have eq10881 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X0))))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op y (M.op (M.op x y) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq10821 X0
       have i₂ := eq1134 (M.op X0 X0)
       grind)
    | exact superpose eq1134 eq10821
    | exact resolve eq10821 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10821
  have eq10913 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op y (M.op (M.op x y) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq52 eq10881
    | exact resolve eq10881 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10881
  have eq11145 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))) = (M.op (M.op X1 (M.op y y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1134 eq6545
    | exact resolve eq6545 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11262 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))) := by
    intro X0
    first
    | (have i₁ := eq6763 X0
       have i₂ := eq11145 X0 y
       grind)
    | exact superpose eq11145 eq6763
    | exact resolve eq6763 eq11145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6763 eq11145
  have eq11328 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))) = (M.op X0 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X0)))))))) := by
    intro X0
    first
    | exact superpose eq11262 eq10651
    | exact resolve eq10651 eq11262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10651 eq11262
  have eq11362 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))) = (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X0))))) := by
    intro X0
    first
    | exact superpose eq7095 eq11328
    | exact resolve eq11328 eq7095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7095 eq11328
  have eq11383 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X0)))))) = X0 := by
    intro X0
    first
    | exact superpose eq11362 eq1462
    | exact resolve eq1462 eq11362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462 eq11362
  have eq12859 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y (M.op (M.op x y) (M.op y X0)))) := by
    intro X0
    first
    | exact superpose eq52 eq11383
    | exact resolve eq11383 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12949 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) = (M.op y (M.op y (M.op (M.op x y) (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq1134 X0
       have i₂ := eq12859 X0
       grind)
    | exact superpose eq12859 eq1134
    | exact resolve eq1134 eq12859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq13142 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ X0))))) := by
    intro X0
    first
    | exact superpose eq12949 eq1152
    | exact resolve eq1152 eq12949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq13158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ X0))))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | exact superpose eq12949 eq1799
    | (have j0 := eq1799 X0 X1
       grind)
    | exact resolve eq1799 eq12949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq13462 : (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq12949 eq1211
    | exact resolve eq1211 eq12949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq13465 : (M.op (σ x) (σ y)) ≠ (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq12949 eq1214
    | exact resolve eq1214 eq12949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq12949
  have eq13977 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X2 X0))) = (M.op (M.op X1 (M.op (M.op y (M.op (M.op x y) X2)) (M.op y (M.op (M.op x y) X2)))) (M.op y (M.op (M.op x y) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6540 eq6545
    | exact resolve eq6545 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13981 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X2 X0))) = (M.op (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) X2))))))) (M.op y (M.op (M.op x y) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13977 X0 X1 X2
       have i₂ := eq12859 (M.op y (M.op sF0 X2))
       grind)
    | exact superpose eq12859 eq13977
    | exact resolve eq13977 eq12859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13977
  have eq14063 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X2 X0))) = (M.op (M.op X1 X2) (M.op y (M.op (M.op x y) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq11383 eq13981
    | exact resolve eq13981 eq11383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11383 eq13981
  have eq14253 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) X0))) = (M.op y (M.op (M.op x y) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq6540 eq10913
    | exact resolve eq10913 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6540 eq10913
  have eq16367 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq52 eq14253
    | exact resolve eq14253 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14253
  have eq16486 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op (M.op x y) (M.op y X0))))))) := by
    intro X0
    first
    | (have i₁ := eq16367 X0
       have i₂ := eq12859 X0
       grind)
    | exact superpose eq12859 eq16367
    | exact resolve eq16367 eq12859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16367
  have eq56542 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 X2) (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6835 (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X2 (M.op X1 X2)) x
       have i₂ := eq1073 X2 X1 x X0
       grind)
    | exact superpose eq1073 eq6835
    | exact resolve eq6835 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6835
  have eq83459 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X2))) (M.op (M.op X3 X2) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1073 X2 X3 X1 (M.op (M.op X0 (M.op X0 X0)) X0)
       have i₂ := eq6557 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq6557 eq1073
    | exact resolve eq1073 eq6557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073 eq6557
  have eq83483 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X2))) (M.op y (M.op (M.op x y) (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq14063 eq83459
    | exact resolve eq83459 eq14063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83459
  have eq83537 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X3 X2)) (M.op X2 X0)))) := by
    intro X0 X2 X3
    first
    | exact superpose eq14063 eq83483
    | exact resolve eq83483 eq14063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14063 eq83483
  have eq83563 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X2 X0)))) := by
    intro X0 X2
    first
    | exact superpose eq7031 eq83537
    | exact resolve eq83537 eq7031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7031 eq83537
  have eq83574 : ∀ X0 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X2 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq83563 X0 X2
       have i₂ := eq56542 X0 X0 X0
       grind)
    | exact superpose eq56542 eq83563
    | exact resolve eq83563 eq56542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56542 eq83563
  have eq83577 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X2 X0)))) := by
    intro X0 X2
    first
    | exact superpose eq52 eq83574
    | exact resolve eq83574 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83574
  have eq83659 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X1)) = (M.op X1 (M.op X0 (M.op y (M.op (M.op x y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1097 X1
       have i₂ := eq83577 X1 X0
       grind)
    | exact superpose eq83577 eq1097
    | exact resolve eq1097 eq83577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83732 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 X1))) = (M.op X0 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6545 (M.op X1 X1) X1 X1
       have i₂ := eq83577 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq83577 eq6545
    | exact resolve eq6545 eq83577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6545
  have eq83788 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 (M.op X1 X1)))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq83732
    | exact resolve eq83732 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83732
  have eq86388 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op (M.op x y) (M.op X1 (M.op y (M.op (M.op x y) X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83788 X1 X0
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq83788
    | exact resolve eq83788 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq83788
  have eq86530 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq516 eq86388
    | exact resolve eq86388 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq95743 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq13158 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13158
    | (have j0 := eq13158 x y
       grind)
    | exact resolve eq13158 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13158
  have eq95795 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq95743
    | exact resolve eq95743 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95743
  have eq95796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95795
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95795
    | exact resolve eq95795 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95795
  have eq95797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95796
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95796
    | exact resolve eq95796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95796
  have eq95798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq95797
    | exact resolve eq95797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95797
  have eq95799 : (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq95798
       have r₂ := eq27
       grind)
    | exact resolve eq95798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95798
  have eq95800 : (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95799
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95799
    | exact resolve eq95799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95799
  have eq95801 : (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95800
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95800
    | exact resolve eq95800 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95800
  have eq95802 : (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq95801
    | exact resolve eq95801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95801
  have eq95803 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95802
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95802
    | exact resolve eq95802 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95802
  have eq95804 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95803
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95803
    | exact resolve eq95803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq95803
  have eq95805 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq95804
    | exact resolve eq95804 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq95804
  have eq95815 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq95805 eq83577
    | exact resolve eq83577 eq95805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95805
  have eq95827 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq6111 eq95815
    | exact resolve eq95815 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95815
  have eq95834 : (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95827
       have i₂ := eq12859 sF2
       grind)
    | exact superpose eq12859 eq95827
    | exact resolve eq95827 eq12859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95827
  have eq95835 : (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq95834
  have eq95840 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq95835 eq13465
    | (have r₁ := eq13465
       have r₂ := eq95835
       grind)
    | exact resolve eq13465 eq95835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13465
  have eq95843 : (M.op y (M.op (M.op x y) (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq95835 eq83659
    | exact resolve eq83659 eq95835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83659 eq95835
  have eq95858 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq95840
  have eq96007 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95858
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq95858
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq95858 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95858
  have eq96079 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96007
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96007
    | exact resolve eq96007 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96007
  have eq96097 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq96079
    | exact resolve eq96079 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96079
  have eq96112 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96097
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96097
    | exact resolve eq96097 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96097
  have eq96113 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq96112
  have eq96122 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96113
    | exact resolve eq96113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq96113
  have eq96123 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq96122
  have eq96496 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ x)))) = (M.op X0 (M.op y (M.op (M.op x y) (M.op X0 (M.op y (M.op (M.op x y) (σ x))))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq95843 eq86530
    | exact resolve eq86530 eq95843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86530 eq95843
  have eq96497 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq86388 eq96496
    | exact resolve eq96496 eq86388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96496
  have eq96511 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (σ x)))))))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq16486 eq96497
    | exact resolve eq96497 eq16486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16486 eq96497
  have eq96523 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ y) (σ x)))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq86388 eq96511
    | exact resolve eq96511 eq86388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86388 eq96511
  have eq97028 : (σ x) = (M.op y (M.op (M.op x y) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq96123 eq96523
    | exact resolve eq96523 eq96123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96123 eq96523
  have eq97055 : (σ x) = (M.op y (M.op (M.op x y) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq97028
  have eq97177 : (τ (σ x)) = (M.op y (M.op (M.op x y) (τ (σ (M.op x y))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq97055 eq7737
    | exact resolve eq7737 eq97055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7737 eq97055
  have eq97207 : (τ (σ x)) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq37 eq97177
    | exact resolve eq97177 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq97177
  have eq97224 : (τ (σ x)) = (M.op y (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76 eq97207
    | exact resolve eq97207 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97207
  have eq97231 : x = (M.op y (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq38 eq97224
    | exact resolve eq97224 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq97224
  have eq98309 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq97231 eq1149
    | exact resolve eq1149 eq97231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97231
  have eq98333 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq98309
  have eq98367 : (M.op x x) = (M.op y (M.op y (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq83577 x y
       have i₂ := eq98333
       grind)
    | exact superpose eq98333 eq83577
    | exact resolve eq83577 eq98333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98333
  have eq98380 : (M.op x x) = (M.op y (M.op y (M.op y (M.op x y)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76 eq98367
    | exact resolve eq98367 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98367
  have eq98400 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1149 eq98380
    | exact resolve eq98380 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98380
  have eq98401 : (M.op x y) = (M.op x x) := by grind
  clear eq98400
  have eq98417 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq98401
       grind)
    | exact superpose eq98401 eq91
    | (have r₁ := eq91
       have r₂ := eq98401
       grind)
    | exact resolve eq91 eq98401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98482 : (k y x) = (M.op y x) := by grind
  clear eq98417
  have eq98505 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13462
       have i₂ := eq98482
       grind)
    | exact superpose eq98482 eq13462
    | exact resolve eq13462 eq98482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13462 eq98482
  have eq98550 : x = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq52 x
       have i₂ := eq98401
       grind)
    | exact superpose eq98401 eq52
    | exact resolve eq52 eq98401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq98557 : (σ (M.op x y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) := by
    first
    | (have i₁ := eq13142 x
       have i₂ := eq98401
       grind)
    | exact superpose eq98401 eq13142
    | exact resolve eq13142 eq98401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13142 eq98401
  have eq104728 : (σ (M.op x y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) := by
    first
    | (have i₁ := eq98557
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq98557
    | exact resolve eq98557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq98557
  have eq104733 : x = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq76 eq98550
    | exact resolve eq98550 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq98550
  have eq106323 : (σ (M.op x y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) := by
    first
    | exact superpose eq20 eq104728
    | exact resolve eq104728 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104728
  have eq106328 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq104733 eq1149
    | exact resolve eq1149 eq104733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq104733
  have eq107300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq106323 eq98505
    | exact resolve eq98505 eq106323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98505
  have eq107593 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq107300
       have r₂ := eq27
       grind)
    | exact resolve eq107300 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107300
  have eq107779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq107593
       have i₂ := eq106328
       grind)
    | exact superpose eq106328 eq107593
    | exact resolve eq107593 eq106328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106328 eq107593
  have eq107916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq107779
    | exact resolve eq107779 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq107779
  have eq108024 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq107916
       have r₂ := eq27
       grind)
    | exact resolve eq107916 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107916
  have eq110327 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq108024 eq83577
    | exact resolve eq83577 eq108024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83577 eq108024
  have eq110338 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6111 eq110327
    | exact resolve eq110327 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6111 eq110327
  have eq110349 : (M.op (σ x) (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op y (σ x))))) := by
    first
    | (have i₁ := eq110338
       have i₂ := eq12859 sF2
       grind)
    | exact superpose eq12859 eq110338
    | exact resolve eq110338 eq12859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12859 eq110338
  have eq110545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106323 eq110349
    | exact resolve eq110349 eq106323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106323 eq110349
  have eq110556 : False := by grind
  exact eq110556

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  clear eq43
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq104
    | exact resolve eq104 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq108
    | exact resolve eq108 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq146 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq236 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq34
    | exact resolve eq34 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq323 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq312 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq312
    | exact resolve eq312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq326 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq323
    | exact resolve eq323 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq323
  have eq517 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq529 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
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
  have eq530 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
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
  have eq532 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  have eq590 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq606 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq611 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq606
    | exact resolve eq606 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq651 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq817 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq16
    | exact resolve eq16 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq968 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq817 X0
       grind)
    | exact superpose eq817 eq50
    | exact resolve eq50 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq1431 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq239 eq50
    | exact resolve eq50 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq236 eq1431
    | exact resolve eq1431 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq1940 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq567 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq567 X0 X0 X0
       grind)
    | exact superpose eq567 eq567
    | exact resolve eq567 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1942 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq239 eq567
    | exact resolve eq567 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq1961 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq567 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq567 X0 X0 X0
       grind)
    | exact superpose eq567 eq567
    | exact resolve eq567 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1992 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq567 X0 X0 X0
       grind)
    | exact superpose eq567 eq14
    | exact resolve eq14 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1993 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq567 X0 X0 X0
       grind)
    | exact superpose eq567 eq50
    | exact resolve eq50 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1994 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq567 X0 X0 X0
       grind)
    | exact superpose eq567 eq51
    | exact resolve eq51 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2001 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq517 (M.op x (M.op x x))
       have i₂ := eq567 x x x
       grind)
    | exact superpose eq567 eq517
    | exact resolve eq517 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq2004 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq600 (M.op x (M.op x x)) x
       have i₂ := eq567 x x x
       grind)
    | exact superpose eq567 eq600
    | exact resolve eq600 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq600
  have eq2041 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq236 eq1942
    | exact resolve eq1942 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq2057 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op y (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1452 eq2041
    | exact resolve eq2041 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq2041
  have eq2218 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq526 X0
       have i₂ := eq1993 X0
       grind)
    | exact superpose eq1993 eq526
    | exact resolve eq526 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq2225 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq530 X0 X0
       have i₂ := eq1993 X0
       grind)
    | exact superpose eq1993 eq530
    | exact resolve eq530 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2246 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1993 eq529
    | exact resolve eq529 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2259 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq529 eq2246
    | exact resolve eq2246 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246
  have eq2298 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq651 eq2218
    | exact resolve eq2218 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq2420 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1994 X0
       have i₂ := eq1993 X0
       grind)
    | exact superpose eq1993 eq1994
    | exact resolve eq1994 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2450 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1994 eq529
    | exact resolve eq529 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2463 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq529 eq2450
    | exact resolve eq2450 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq2450
  have eq2544 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2001 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2001
    | exact resolve eq2001 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2590 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2544 X0 X1
       have i₂ := eq1993 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1993 eq2544
    | exact resolve eq2544 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544
  have eq2607 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2590 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2590
    | exact resolve eq2590 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2772 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2004 X0 X1
       have i₂ := eq1993 X0
       grind)
    | exact superpose eq1993 eq2004
    | exact resolve eq2004 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq3011 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq968 eq2218
    | exact resolve eq2218 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq2218
  have eq5344 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X1 X0 X1 X0
       have i₂ := eq611 X0 X1
       grind)
    | exact superpose eq611 eq532
    | exact resolve eq532 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq611
  have eq30158 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq590 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1992 X0 X0 X1
       grind)
    | exact superpose eq1992 eq590
    | exact resolve eq590 eq1992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq30246 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30158 X0 X1 x x x
       have i₂ := eq590 X0 X0 x x x
       grind)
    | exact superpose eq590 eq30158
    | exact resolve eq30158 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq30158
  have eq44289 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2607 eq14
    | exact resolve eq14 eq2607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq45089 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1940 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1940
    | (have j0 := eq1940 y x X0
       grind)
    | exact resolve eq1940 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq47038 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq44289 eq1961
    | exact resolve eq1961 eq44289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq47633 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq236 eq47038
    | exact resolve eq47038 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq47038
  have eq47939 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47633 X0 X1
       have i₂ := eq1993 (M.op X0 (M.op y X0))
       grind)
    | exact superpose eq1993 eq47633
    | exact resolve eq47633 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993 eq47633
  have eq48105 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq530 eq47939
    | exact resolve eq47939 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq47939
  have eq50793 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op y (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq48105 eq2057
    | exact resolve eq2057 eq48105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057 eq48105
  have eq70997 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45089 y
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq45089
    | exact resolve eq45089 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq45089
  have eq71147 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70997
       have i₂ := eq30246 (M.op y x) y
       grind)
    | exact superpose eq30246 eq70997
    | exact resolve eq70997 eq30246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30246 eq70997
  have eq71182 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71147
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq71147
    | exact resolve eq71147 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq71147
  have eq71200 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq44289 eq71182
    | exact resolve eq71182 eq44289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44289 eq71182
  have eq71231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71200 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq71200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71200
  have eq71232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq71231
    | exact resolve eq71231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71231
  have eq71243 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq71232
       have r₂ := eq27
       grind)
    | exact resolve eq71232 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71232
  have eq71247 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq71243
    | exact resolve eq71243 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71243
  have eq71253 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71247 eq146
    | exact resolve eq146 eq71247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq71271 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71247 eq50
    | exact resolve eq50 eq71247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq71247
  have eq72564 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71271 eq5344
    | exact resolve eq5344 eq71271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5344 eq71271
  have eq72660 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq72564
    | exact resolve eq72564 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72564
  have eq72702 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq72660 eq2772
    | exact resolve eq2772 eq72660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2772 eq72660
  have eq79575 : (M.op (σ y) (σ x)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq72702 eq2420
    | exact resolve eq2420 eq72702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420 eq72702
  have eq79682 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2225 eq79575
    | exact resolve eq79575 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225 eq79575
  have eq79710 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq79682 eq71253
    | exact resolve eq71253 eq79682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71253 eq79682
  have eq79781 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq79710
  have eq79786 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71 eq79781
    | exact resolve eq79781 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79781
  have eq81520 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50793 X0 y
       have i₂ := eq79786
       grind)
    | exact superpose eq79786 eq50793
    | exact resolve eq50793 eq79786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79786
  have eq81609 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq50793 eq81520
    | exact resolve eq81520 eq50793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50793 eq81520
  have eq81610 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq81609
  have eq81822 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq81610 eq2463
    | exact resolve eq2463 eq81610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq81869 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq81822
    | exact resolve eq81822 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81822
  have eq84616 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq81869 eq3011
    | exact resolve eq3011 eq81869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011 eq81869
  have eq84730 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq84616
    | exact resolve eq84616 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq84616
  have eq86857 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq81610 eq84730
    | exact resolve eq84730 eq81610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81610 eq84730
  have eq86934 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq86857
  have eq86960 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq86934
    | exact resolve eq86934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq86934
  have eq86976 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86960
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86960
    | exact resolve eq86960 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86960
  have eq86977 : x = (M.op x y) ∨ x = y := by grind
  clear eq86976
  have eq86994 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq86977 eq20
    | exact resolve eq20 eq86977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87114 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq86977 eq2259
    | exact resolve eq2259 eq86977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259 eq86977
  have eq87208 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq87114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87114
    | exact resolve eq87114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87114
  have eq87272 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq86994
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86994
    | exact resolve eq86994 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86994
  have eq87306 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq87272 eq26
    | exact resolve eq26 eq87272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87272
  have eq87632 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2298 y
       have i₂ := eq87208
       grind)
    | exact superpose eq87208 eq2298
    | exact resolve eq2298 eq87208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298 eq87208
  have eq87762 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq87632
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87632
    | exact resolve eq87632 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87632
  have eq87837 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq87762
    | exact resolve eq87762 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87762
  have eq88330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq87837 eq87306
    | exact resolve eq87306 eq87837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87306 eq87837
  have eq88396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq88330
  have eq88417 : x = y := by
    first
    | (have r₁ := eq88396
       have r₂ := eq27
       grind)
    | exact resolve eq88396 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88396
  have eq89268 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq88417
       grind)
    | exact superpose eq88417 eq18
    | exact resolve eq18 eq88417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq89269 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq88417
       grind)
    | exact superpose eq88417 eq24
    | exact resolve eq24 eq88417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq88417
  have eq89545 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq89269
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq89269
    | exact resolve eq89269 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq89269
  have eq89593 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq89545 eq26
    | exact resolve eq26 eq89545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq89545
  have eq90406 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq89593 eq71
    | exact resolve eq71 eq89593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq89593
  have eq90708 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq90406
       have i₂ := eq89268
       grind)
    | exact superpose eq89268 eq90406
    | exact resolve eq90406 eq89268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89268 eq90406
  have eq90852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90708 eq15
    | exact resolve eq15 eq90708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90708
  have eq90966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq90852
    | exact resolve eq90852 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq90852
  have eq91007 : False := by grind
  exact eq91007

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq91 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
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
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126
    | (have j0 := eq126 (σ X0) (σ X1)
       grind)
    | exact resolve eq126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq91 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq174 : ∀ X1 X3 X4 : G, (M.op (M.op X1 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq29 X3 x (M.op (M.op x x) (M.op X1 X1)) X4
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq207 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X1 (M.op x (M.op x x))
       have i₂ := eq174 x x x
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq241 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq135 x y
       grind)
    | exact superpose eq135 eq16
    | (have j1 := eq135 x y
       grind)
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq716 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X0 (M.op X0 X0) X2 X1
       have i₂ := eq207 X0 X0
       grind)
    | exact superpose eq207 eq99
    | exact resolve eq99 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq718 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq99 X0 X0 x (M.op X0 X0)
       have i₂ := eq174 x X0 X0
       grind)
    | exact superpose eq174 eq99
    | exact resolve eq99 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq749 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq718 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq718
    | exact resolve eq718 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq857 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 (M.op X0 X1) X1 X3 X2
       have i₂ := eq716 X1 X1 X0
       grind)
    | exact superpose eq716 eq99
    | exact resolve eq99 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq869 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1 x x
       have i₂ := eq99 X1 X1 x x
       grind)
    | exact superpose eq99 eq857
    | exact resolve eq857 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq857
  have eq1566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq241
       have i₂ := eq126 x y
       grind)
    | exact superpose eq126 eq241
    | (have j1 := eq126 (σ x) (σ y)
       grind)
    | exact resolve eq241 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq241
  have eq1567 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1566
  have eq1581 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq869 (σ x) (σ y)
       have i₂ := eq1567
       grind)
    | exact superpose eq1567 eq869
    | exact resolve eq869 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1585 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1581
       have i₂ := eq60 y
       grind)
    | exact superpose eq60 eq1581
    | exact resolve eq1581 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1581
  have eq11221 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1567
       have i₂ := eq1585
       grind)
    | exact superpose eq1585 eq1567
    | exact resolve eq1567 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567 eq1585
  have eq11273 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq11221
  have eq11344 : (M.op y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11273
       grind)
    | exact superpose eq11273 eq10
    | exact resolve eq10 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11273
  have eq11384 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11344
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11344
    | exact resolve eq11344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11344
  have eq11499 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq869 y y
       have i₂ := eq11384
       grind)
    | exact superpose eq11384 eq869
    | exact resolve eq869 eq11384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11384
  have eq11518 : x = (M.op x y) := by grind
  clear eq11499
  have eq11555 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq869 x y
       have i₂ := eq11518
       grind)
    | exact superpose eq11518 eq869
    | exact resolve eq869 eq11518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq11584 : x = (M.op y y) := by
    first
    | (have i₁ := eq11555
       have i₂ := eq11518
       grind)
    | exact superpose eq11518 eq11555
    | exact resolve eq11555 eq11518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11555
  have eq11640 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq749 y
       have i₂ := eq11584
       grind)
    | exact superpose eq11584 eq749
    | exact resolve eq749 eq11584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq11584
  have eq12023 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11640
       grind)
    | exact superpose eq11640 eq16
    | exact resolve eq16 eq11640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11640
  have eq12077 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq12023
       have i₂ := eq11518
       grind)
    | exact superpose eq11518 eq12023
    | exact resolve eq12023 eq11518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11518 eq12023
  have eq12078 : False := by grind
  exact eq12078

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pxy_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
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
  have eq63 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y x) := by
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
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (k y x) := by
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
  have eq78 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq99 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq99
    | exact resolve eq99 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq103
    | exact resolve eq103 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq103
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq236 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq236 eq50
    | exact resolve eq50 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq529 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
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
  have eq580 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0) (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq53
    | exact resolve eq53 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq580 X0
       have i₂ := eq73 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq580
    | exact resolve eq580 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq599 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq590 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq590
    | exact resolve eq590 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq732 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  clear eq52
  have eq989 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq85
  have eq1047 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq989 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1441 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq239 eq50
    | exact resolve eq50 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq1464 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq236 eq1441
    | exact resolve eq1441 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1876 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1464 eq243
    | exact resolve eq243 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq1464
  have eq1966 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq732 X0 X0 X0
       grind)
    | exact superpose eq732 eq50
    | exact resolve eq50 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1967 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq732 X0 X0 X0
       grind)
    | exact superpose eq732 eq51
    | exact resolve eq51 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq2236 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq526 X0
       have i₂ := eq1966 X0
       grind)
    | exact superpose eq1966 eq526
    | exact resolve eq526 eq1966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2264 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq51 sF4
       have i₂ := eq1966 sF4
       grind)
    | exact superpose eq1966 eq51
    | exact resolve eq51 eq1966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1966
  have eq2315 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2236
    | exact resolve eq2236 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2484 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1967 eq529
    | exact resolve eq529 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq2497 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq529 eq2484
    | exact resolve eq2484 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq2484
  have eq21042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq21042
    | exact resolve eq21042 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21042
  have eq21054 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq21043
       have r₂ := eq27
       grind)
    | exact resolve eq21043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21043
  have eq21058 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq21054
    | exact resolve eq21054 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21054
  have eq21062 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq21058
    | exact resolve eq21058 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21058
  have eq21064 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21062 eq64
    | (have r₁ := eq64
       have r₂ := eq21062
       grind)
    | exact resolve eq64 eq21062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21074 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21062 eq50
    | exact resolve eq50 eq21062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21062
  have eq21155 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq21064
  have eq21616 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21074 eq2264
    | exact resolve eq2264 eq21074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21074
  have eq22032 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21155 eq116
    | exact resolve eq116 eq21155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21155
  have eq22045 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22032
  have eq22194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22045 eq21616
    | exact resolve eq21616 eq22045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21616
  have eq22232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq22194
  have eq22238 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22232
       have r₂ := eq27
       grind)
    | exact resolve eq22232 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22232
  have eq22241 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq22238
       grind)
    | exact superpose eq22238 eq63
    | (have r₁ := eq63
       have r₂ := eq22238
       grind)
    | exact resolve eq63 eq22238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22242 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq22238
       grind)
    | exact superpose eq22238 eq72
    | exact resolve eq72 eq22238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22252 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq22238
       grind)
    | exact superpose eq22238 eq50
    | exact resolve eq50 eq22238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22238
  have eq22332 : (k y x) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22241
  have eq22360 : x = (M.op y (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq236 eq22252
    | exact resolve eq22252 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22252
  have eq22367 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22242
    | exact resolve eq22242 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22242
  have eq23205 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq22332
       grind)
    | exact superpose eq22332 eq98
    | exact resolve eq98 eq22332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22332
  have eq23554 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22360 eq1876
    | exact resolve eq1876 eq22360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22360
  have eq24155 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23205
       have i₂ := eq23554
       grind)
    | exact superpose eq23554 eq23205
    | exact resolve eq23205 eq23554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23205 eq23554
  have eq24206 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24155
  have eq24220 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq24206
    | exact resolve eq24206 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24206
  have eq24239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24220 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq24220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24220
  have eq24242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24239
    | exact resolve eq24239 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24239
  have eq24253 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24242
       have r₂ := eq27
       grind)
    | exact resolve eq24242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24242
  have eq24257 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24253
    | exact resolve eq24253 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24253
  have eq24258 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq24257
  have eq24263 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq24258
    | exact resolve eq24258 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24258
  have eq24355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24263 eq22367
    | exact resolve eq22367 eq24263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22367 eq24263
  have eq24439 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24355
  have eq24459 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24439
       have r₂ := eq27
       grind)
    | exact resolve eq24439 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24439
  have eq24465 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24459 eq27
    | exact resolve eq27 eq24459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24467 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24459 eq78
    | (have r₁ := eq78
       have r₂ := eq24459
       grind)
    | exact resolve eq78 eq24459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq24499 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq24467
  have eq24817 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24499 eq112
    | exact resolve eq112 eq24499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq24818 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24499 eq116
    | exact resolve eq116 eq24499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq24499
  have eq24837 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq24818
  have eq24850 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24837
       have r₂ := eq24465
       grind)
    | exact resolve eq24837 eq24465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24837
  have eq24851 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq24817
    | exact resolve eq24817 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24817
  have eq24863 : (τ (σ y)) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24850 eq71
    | exact resolve eq71 eq24850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq24889 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24850 eq526
    | exact resolve eq526 eq24850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq24850
  have eq24990 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq24889
    | exact resolve eq24889 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24889
  have eq25002 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq24863
    | exact resolve eq24863 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24863
  have eq25076 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24851 eq2315
    | exact resolve eq2315 eq24851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq25734 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24459 eq24990
    | exact resolve eq24990 eq24459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24990
  have eq25779 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq25734
  have eq25788 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq25779
    | exact resolve eq25779 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25779
  have eq26043 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq63
       have i₂ := eq25788
       grind)
    | exact superpose eq25788 eq63
    | (have r₁ := eq63
       have r₂ := eq25788
       grind)
    | exact resolve eq63 eq25788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq26044 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq25788
       grind)
    | exact superpose eq25788 eq72
    | exact resolve eq72 eq25788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26054 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq25788
       grind)
    | exact superpose eq25788 eq50
    | exact resolve eq50 eq25788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25788
  have eq26139 : (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq26043
  have eq26169 : x = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq236 eq26054
    | exact resolve eq26054 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq26054
  have eq26176 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq26044
    | exact resolve eq26044 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26044
  have eq26274 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26176 eq24851
    | exact resolve eq24851 eq26176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24851 eq26176
  have eq26363 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26274
  have eq26379 : y = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26363
       have r₂ := eq24465
       grind)
    | exact resolve eq26363 eq24465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26363
  have eq27029 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq25002
       grind)
    | exact superpose eq25002 eq72
    | exact resolve eq72 eq25002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25002
  have eq27165 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq27029
    | exact resolve eq27029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27029
  have eq27182 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22045 eq25076
    | exact resolve eq25076 eq22045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22045 eq25076
  have eq27229 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27182
  have eq27244 : y = (k y x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq27229
       have r₂ := eq24465
       grind)
    | exact resolve eq27229 eq24465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24465 eq27229
  have eq27250 : (M.op x y) = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq27244
       have r₂ := eq77
       grind)
    | exact resolve eq27244 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq27244
  have eq29561 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26379
       have i₂ := eq26139
       grind)
    | exact superpose eq26139 eq26379
    | exact resolve eq26379 eq26139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26139 eq26379
  have eq29568 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29561
  have eq30514 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26169 eq1876
    | exact resolve eq1876 eq26169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876 eq26169
  have eq30729 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29568
       have i₂ := eq30514
       grind)
    | exact superpose eq30514 eq29568
    | exact resolve eq29568 eq30514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29568 eq30514
  have eq30770 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq30729
  have eq30827 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30770 eq2497
    | exact resolve eq2497 eq30770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq30840 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30770 eq24459
    | exact resolve eq24459 eq30770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24459 eq30770
  have eq30849 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq30840
  have eq30864 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq30827
    | exact resolve eq30827 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30827
  have eq31014 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30849 eq26
    | exact resolve eq26 eq30849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30849
  have eq32057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31014 eq27165
    | exact resolve eq27165 eq31014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27165 eq31014
  have eq32148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq32057
  have eq32177 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq32148
       have r₂ := eq27
       grind)
    | exact resolve eq32148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32148
  have eq32615 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq32177
       grind)
    | exact superpose eq32177 eq53
    | exact resolve eq53 eq32177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq32177
  have eq32679 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32615
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32615
    | exact resolve eq32615 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32615
  have eq33675 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq32679
       grind)
    | exact superpose eq32679 eq105
    | exact resolve eq105 eq32679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq32679
  have eq33814 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq33675
    | exact resolve eq33675 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33675
  have eq34706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33814 eq30864
    | exact resolve eq30864 eq33814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30864 eq33814
  have eq34801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq34706
  have eq34823 : y = (M.op x y) := by
    first
    | (have r₁ := eq34801
       have r₂ := eq27
       grind)
    | exact resolve eq34801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34801
  have eq34852 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq34823 eq20
    | exact resolve eq20 eq34823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34938 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op y (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq34823 eq2264
    | exact resolve eq2264 eq34823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq35019 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34852
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34852
    | exact resolve eq34852 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34852
  have eq35041 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq35019 eq26
    | exact resolve eq26 eq35019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq37119 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op y (M.op y (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq35019 eq34938
    | exact resolve eq34938 eq35019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34938
  have eq43221 : (σ (M.op x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq599 x
       have i₂ := eq27250
       grind)
    | exact superpose eq27250 eq599
    | exact resolve eq599 eq27250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq27250
  have eq43338 : (σ (M.op x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq43221
    | exact resolve eq43221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43221
  have eq43464 : (σ (M.op x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43338
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43338
    | exact resolve eq43338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43338
  have eq43577 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x y))) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35041 eq43464
    | exact resolve eq43464 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43464
  have eq43652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34823 eq43577
    | exact resolve eq43577 eq34823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43577
  have eq43689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43652
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43652
    | exact resolve eq43652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq43652
  have eq43723 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq43689
    | exact resolve eq43689 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq43689
  have eq43740 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq43723
       have r₂ := eq27
       grind)
    | exact resolve eq43723 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43723
  have eq43746 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq35019 eq43740
    | exact resolve eq43740 eq35019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43740
  have eq43750 : y = (k y x) := by
    first
    | (have r₁ := eq43746
       have r₂ := eq27
       grind)
    | exact resolve eq43746 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43746
  have eq43761 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq43750
       grind)
    | exact superpose eq43750 eq98
    | exact resolve eq98 eq43750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq43777 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1047 x y
       have i₂ := eq43750
       grind)
    | exact superpose eq43750 eq1047
    | (have j0 := eq1047 x y
       grind)
    | exact resolve eq1047 eq43750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq43750
  have eq43780 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43777
  have eq43785 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43780
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq43780
    | exact resolve eq43780 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq43780
  have eq43797 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq35019 eq43761
    | exact resolve eq43761 eq35019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43761
  have eq43799 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43785
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43785
    | exact resolve eq43785 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43785
  have eq43811 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq43797
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43797
    | exact resolve eq43797 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43797
  have eq43812 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35019 eq43799
    | exact resolve eq43799 eq35019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43799
  have eq43824 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq35019 eq43811
    | exact resolve eq43811 eq35019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43811
  have eq43825 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43812
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43812
    | exact resolve eq43812 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43812
  have eq43832 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35041 eq43825
    | exact resolve eq43825 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43825
  have eq43836 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43832
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43832
    | exact resolve eq43832 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43832
  have eq43840 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35019 eq43836
    | exact resolve eq43836 eq35019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43836
  have eq43844 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43840
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43840
    | exact resolve eq43840 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq43840
  have eq43848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35041 eq43844
    | exact resolve eq43844 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35041 eq43844
  have eq43852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq43848
       have r₂ := eq27
       grind)
    | exact resolve eq43848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43848
  have eq43936 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq43852 eq64
    | (have r₁ := eq64
       have r₂ := eq43852
       grind)
    | exact resolve eq64 eq43852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq43955 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq43852 eq50
    | exact resolve eq50 eq43852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq43852
  have eq44058 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
  clear eq43936
  have eq44108 : (σ x) = (M.op y (M.op y (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq34823 eq43955
    | exact resolve eq43955 eq34823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34823 eq43955
  have eq44114 : (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq35019 eq44058
    | exact resolve eq44058 eq35019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35019 eq44058
  have eq44142 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq43824 eq44114
    | exact resolve eq44114 eq43824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43824 eq44114
  have eq45241 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq44108 eq37119
    | exact resolve eq37119 eq44108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37119 eq44108
  have eq45325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44142 eq45241
    | exact resolve eq45241 eq44142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44142 eq45241
  have eq45342 : False := by grind
  exact eq45342

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq63 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y x) := by
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
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq99 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq103 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq99
    | exact resolve eq99 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq103
    | exact resolve eq103 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq103
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq144 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq236 eq50
    | exact resolve eq50 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq529 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
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
  clear eq53
  have eq566 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  clear eq52
  have eq1407 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq239 eq50
    | exact resolve eq50 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq1428 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq236 eq1407
    | exact resolve eq1407 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1707 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1428 eq243
    | exact resolve eq243 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq1428
  have eq1939 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq566 X0 X0 X0
       grind)
    | exact superpose eq566 eq50
    | exact resolve eq50 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1940 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq566 X0 X0 X0
       grind)
    | exact superpose eq566 eq51
    | exact resolve eq51 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq2144 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq526 X0
       have i₂ := eq1939 X0
       grind)
    | exact superpose eq1939 eq526
    | exact resolve eq526 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq2170 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq51 sF4
       have i₂ := eq1939 sF4
       grind)
    | exact superpose eq1939 eq51
    | exact resolve eq51 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2172 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1939 eq529
    | exact resolve eq529 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq2184 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq529 eq2172
    | exact resolve eq2172 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2219 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2144
    | exact resolve eq2144 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144
  have eq2386 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1940 eq529
    | exact resolve eq529 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq2398 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq529 eq2386
    | exact resolve eq2386 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq2386
  have eq18821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq18821
    | exact resolve eq18821 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18821
  have eq18833 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq18822
       have r₂ := eq27
       grind)
    | exact resolve eq18822 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18822
  have eq18837 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq18833
    | exact resolve eq18833 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18833
  have eq18841 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq18837
    | exact resolve eq18837 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18837
  have eq18843 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18841 eq64
    | (have r₁ := eq64
       have r₂ := eq18841
       grind)
    | exact resolve eq64 eq18841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq18853 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18841 eq50
    | exact resolve eq50 eq18841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18841
  have eq18925 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq18843
  have eq19375 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18853 eq2170
    | exact resolve eq2170 eq18853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq18853
  have eq19768 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18925 eq116
    | exact resolve eq116 eq18925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq18925
  have eq19780 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19768
  have eq19925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19780 eq19375
    | exact resolve eq19375 eq19780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19375 eq19780
  have eq19959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq19925
  have eq19965 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19959
       have r₂ := eq27
       grind)
    | exact resolve eq19959 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19959
  have eq19968 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq19965
       grind)
    | exact superpose eq19965 eq63
    | (have r₁ := eq63
       have r₂ := eq19965
       grind)
    | exact resolve eq63 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq19969 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq19965
       grind)
    | exact superpose eq19965 eq72
    | exact resolve eq72 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq19979 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq19965
       grind)
    | exact superpose eq19965 eq50
    | exact resolve eq50 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq19965
  have eq20050 : (k y x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19968
  have eq20079 : x = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq236 eq19979
    | exact resolve eq19979 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq19979
  have eq20086 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19969
    | exact resolve eq19969 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19969
  have eq20882 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq20050
       grind)
    | exact superpose eq20050 eq98
    | exact resolve eq98 eq20050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq20050
  have eq21209 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20079 eq1707
    | exact resolve eq1707 eq20079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq20079
  have eq21758 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20882
       have i₂ := eq21209
       grind)
    | exact superpose eq21209 eq20882
    | exact resolve eq20882 eq21209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20882 eq21209
  have eq21809 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21758
  have eq21823 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21809
    | exact resolve eq21809 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21809
  have eq21841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21823 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq21823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21823
  have eq21844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21841
    | exact resolve eq21841 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21841
  have eq21855 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq21844
       have r₂ := eq27
       grind)
    | exact resolve eq21844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21844
  have eq21859 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21855
    | exact resolve eq21855 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21855
  have eq21860 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq21859
  have eq21865 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq21860
    | exact resolve eq21860 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21860
  have eq21944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21865 eq20086
    | exact resolve eq20086 eq21865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20086 eq21865
  have eq22019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21944
  have eq22041 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22019
       have r₂ := eq27
       grind)
    | exact resolve eq22019 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22019
  have eq22081 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22041 eq2398
    | exact resolve eq2398 eq22041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq22087 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq22081
    | exact resolve eq22081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22081
  have eq22093 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22087 eq144
    | exact resolve eq144 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq22087
  have eq22240 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2219 y
       have i₂ := eq22093
       grind)
    | exact superpose eq22093 eq2219
    | exact resolve eq2219 eq22093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22093
  have eq22508 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22041 eq22240
    | exact resolve eq22240 eq22041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22041 eq22240
  have eq22543 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by grind
  clear eq22508
  have eq22550 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq22543
    | exact resolve eq22543 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq22543
  have eq22553 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22550
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22550
    | exact resolve eq22550 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22550
  have eq22554 : x = (M.op x y) := by grind
  clear eq22553
  have eq22557 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq22554 eq20
    | exact resolve eq20 eq22554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22634 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq22554 eq2184
    | exact resolve eq2184 eq22554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184
  have eq22653 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq22634
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22634
    | exact resolve eq22634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq22634
  have eq22701 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22557
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22557
    | exact resolve eq22557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22557
  have eq22702 : x = (M.op y y) := by
    first
    | exact superpose eq22554 eq22653
    | exact resolve eq22653 eq22554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22554 eq22653
  have eq22719 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq22701 eq26
    | exact resolve eq26 eq22701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq22918 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq22702
       grind)
    | exact superpose eq22702 eq105
    | exact resolve eq105 eq22702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq22702
  have eq23038 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq22918
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22918
    | exact resolve eq22918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22918
  have eq23055 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq22701 eq23038
    | exact resolve eq23038 eq22701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22701 eq23038
  have eq23162 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23055 eq2219
    | exact resolve eq2219 eq23055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219 eq23055
  have eq23218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22719 eq23162
    | exact resolve eq23162 eq22719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22719 eq23162
  have eq23246 : False := by grind
  exact eq23246
