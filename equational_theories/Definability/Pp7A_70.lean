import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3874`: `x ◇ x = (x ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pyy_pxy_pyx_pxy_Equation3874 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13 (σ y) (σ x)
       grind)
    | exact superpose eq13 eq16
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12 (σ x) (σ y)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19
    | exact resolve eq19 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq17
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17
    | exact resolve eq17 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq74 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq21
       have i₂ := eq13 (σ x) (σ y)
       grind)
    | exact superpose eq13 eq21
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq21 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq21
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq79 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by grind
  clear eq77
  have eq81 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq74
  have eq82 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq79
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq84 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq81
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq81
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq86 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq84
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq84
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq86
    | exact resolve eq86 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ (k x y))) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq9
    | exact resolve eq9 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq117 : ∀ X0 : G, (M.op (M.op X0 (σ (k x y))) (σ x)) = (k X0 X0) ∨ (M.op (M.op X0 (σ (k x y))) (σ x)) ≠ (M.op (M.op X0 (σ (k x y))) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq12
    | exact resolve eq12 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (M.op (M.op X0 (σ (k x y))) (σ x)) = (k X0 X0) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    intro X0
    first
    | (have j0 := eq117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq135 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq98
    | exact resolve eq98 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq124
  have eq141 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq144 : ∀ X0 : G, (σ (k y x)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq141 X0
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq141
    | (have j0 := eq141 X0
       have j1 := eq13 x y
       grind)
    | exact resolve eq141 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq146 : ∀ X0 : G, (M.op x y) = (M.op y x) ∨ (M.op x x) ≠ (M.op y y) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq148 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have r₁ := eq22
       have r₂ := eq20
       grind)
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq151 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq148
       grind)
    | exact superpose eq148 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | exact resolve eq12 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq153 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by grind
  clear eq151
  have eq157 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq153
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq153
    | exact resolve eq153 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq160 : (σ (k y y)) = (k (σ x) (σ x)) ∨ (σ (k y y)) ≠ (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq157
       grind)
    | exact superpose eq157 eq12
    | exact resolve eq12 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq162 : (σ (k y y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by grind
  clear eq160
  have eq164 : (σ (k y y)) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq162
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq162
    | exact resolve eq162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq168 : (k y y) = (τ (σ (k x x))) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq164
       grind)
    | exact superpose eq164 eq10
    | exact resolve eq10 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq169 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq168
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq168
    | exact resolve eq168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq172 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k y y) = (k x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq169
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq169
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq169 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k y y) = (k x x) ∨ (M.op x y) ≠ (M.op y x) := by
    first
    | (have i₁ := eq169
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq169
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq169 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq175 : (k y y) = (k x x) ∨ (M.op x y) ≠ (M.op y x) := by grind
  clear eq174
  have eq176 : (k y y) = (k x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq172
  have eq217 : (k y y) = (k x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq176
       have r₂ := eq175
       grind)
    | exact resolve eq176 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq219 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (M.op x x) ≠ (M.op y y) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq146 X0
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq146
    | (have j0 := eq146 X0
       have j1 := eq13 x y
       grind)
    | exact resolve eq146 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq224 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (M.op x x) ≠ (M.op y y) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq226 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq224 X0
       have j1 := eq14 x y
       grind)
    | (have r₁ := eq224 X0
       have r₂ := eq14 x y
       grind)
    | (have r₁ := eq224 X0
       have r₂ := eq14 y x
       grind)
    | exact resolve eq224 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq227 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq226 X0
       have j1 := eq12 x y
       grind)
    | (have r₁ := eq226 X0
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq226 X0
       have r₂ := eq12 y x
       grind)
    | exact resolve eq226 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq233 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (k x y)) x) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq227 X1
       grind)
    | exact superpose eq227 eq9
    | (have j1 := eq227 X1
       grind)
    | exact resolve eq9 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq249 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X0 (k x y)) x) ∨ (M.op (M.op X0 (k x y)) x) ≠ (M.op (M.op X0 (k x y)) x) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq233 X0 X1
       grind)
    | exact superpose eq233 eq12
    | (have j0 := eq12 X1 X1
       have j1 := eq233 X0 X1
       grind)
    | exact resolve eq12 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, (k X0 X0) ≠ (M.op (M.op X0 (k x y)) x) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq233 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq258 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X0 (k x y)) x) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq281 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq257 X0
       have i₂ := eq258 X0 X1
       grind)
    | exact superpose eq258 eq257
    | (have j0 := eq257 X0
       have j1 := eq258 X0 X0
       grind)
    | (have r₁ := eq257 X0
       have r₂ := eq258 X0 X1
       grind)
    | exact resolve eq257 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq258
  have eq287 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq281 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq314 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq287 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq314 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq445 : (M.op (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq315 (σ y)
       grind)
    | exact superpose eq315 eq82
    | exact resolve eq82 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq446 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq445
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq445
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq447 : (σ (k y y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq446
       have i₂ := eq315 (σ x)
       grind)
    | exact superpose eq315 eq446
    | exact resolve eq446 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq448 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y y)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq447
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq447
    | exact resolve eq447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq725 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y y)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq448
       grind)
    | exact superpose eq448 eq16
    | exact resolve eq16 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq739 : (σ (k y y)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by grind
  clear eq725
  have eq2142 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq739
       have i₂ := eq217
       grind)
    | exact superpose eq217 eq739
    | exact resolve eq739 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2147 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq2142
  have eq2148 : (k y y) = (M.op x x) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq2147
       have i₂ := eq315 y
       grind)
    | exact superpose eq315 eq2147
    | exact resolve eq2147 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147
  have eq2149 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq2148
       have i₂ := eq315 x
       grind)
    | exact superpose eq315 eq2148
    | exact resolve eq2148 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq28776 : (σ (k y x)) ≠ (σ (k y x)) ∨ (k y y) = (k x x) ∨ (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2149
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2149
    | (have j1 := eq13 x y
       grind)
    | exact resolve eq2149 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq28778 : (k y y) = (k x x) ∨ (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq28776
  have eq28779 : (k y y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq28778
       have r₂ := eq217
       grind)
    | exact resolve eq28778 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq28778
  have eq28781 : (k y y) = (k x x) := by
    first
    | (have r₁ := eq28779
       have r₂ := eq175
       grind)
    | exact resolve eq28779 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq28779
  have eq28783 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq739
       have i₂ := eq28781
       grind)
    | exact superpose eq28781 eq739
    | exact resolve eq739 eq28781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq28878 : (σ (M.op x y)) ≠ (σ (k y x)) := by grind
  clear eq28783
  have eq28884 : (σ (k y x)) ≠ (σ (k y x)) ∨ (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28878
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq28878
    | (have j1 := eq13 x y
       grind)
    | exact resolve eq28878 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28886 : (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq28884
  have eq28887 : (k y y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28886
       have i₂ := eq315 y
       grind)
    | exact superpose eq315 eq28886
    | exact resolve eq28886 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28886
  have eq28889 : (k y y) ≠ (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28887
       have i₂ := eq315 x
       grind)
    | exact superpose eq315 eq28887
    | exact resolve eq28887 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq28887
  have eq28891 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq28889
       have r₂ := eq28781
       grind)
    | exact resolve eq28889 eq28781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28781 eq28889
  have eq28907 : (M.op x y) = (k y x) ∨ (M.op x y) ≠ (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq28891
       grind)
    | exact superpose eq28891 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq28891
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq28891
       grind)
    | exact resolve eq12 eq28891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28891
  have eq28940 : (M.op x y) = (k y x) := by grind
  clear eq28907
  have eq28949 : (σ (k y x)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq28878
       have i₂ := eq28940
       grind)
    | exact superpose eq28940 eq28878
    | exact resolve eq28878 eq28940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28878 eq28940
  have eq28985 : False := by grind
  exact eq28985

/-- `Equation3874`: `x ◇ x = (x ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3874 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3874.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : x ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq1143 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  clear eq18
  have eq1163 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1282 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq40
    | exact resolve eq40 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1283 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1282
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1282
    | exact resolve eq1282 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1285 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1283
    | exact resolve eq1283 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1285 eq1163
    | exact resolve eq1163 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1300 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1293
       have r₂ := eq27
       grind)
    | exact resolve eq1293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1311 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1300 eq1143
    | (have r₁ := eq1143
       have r₂ := eq1300
       grind)
    | exact resolve eq1143 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1300
  have eq1313 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1311
  have eq1314 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1313
       have r₂ := eq1312
       grind)
    | exact resolve eq1313 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312 eq1313
  have eq1322 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1314 eq152
    | exact resolve eq152 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1314
  have eq1327 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1322
    | exact resolve eq1322 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1322
  have eq1330 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1327
       have r₂ := eq1142
       grind)
    | exact resolve eq1327 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1334 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq1330
       grind)
    | exact superpose eq1330 eq1162
    | exact resolve eq1162 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1336 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1330
       grind)
    | exact superpose eq1330 eq40
    | exact resolve eq40 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1330
  have eq1337 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1334
  have eq1339 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1336
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1336
    | exact resolve eq1336 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1344 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1337 eq175
    | (have r₁ := eq175
       have r₂ := eq1337
       grind)
    | exact resolve eq175 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1350 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1344
  have eq1355 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1339 eq1163
    | exact resolve eq1163 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1359 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1355
  have eq1368 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1359 eq27
    | exact resolve eq27 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq1390 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1350 eq90
    | exact resolve eq90 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq1401 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1390
    | exact resolve eq1390 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1404 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1401
       have r₂ := eq174
       grind)
    | exact resolve eq1401 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1410 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq1404
       grind)
    | exact superpose eq1404 eq1162
    | exact resolve eq1162 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq1404
  have eq1413 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1410
  have eq1419 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1413
       grind)
    | exact superpose eq1413 eq24
    | exact resolve eq24 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1422 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1142
       have i₂ := eq1413
       grind)
    | exact superpose eq1413 eq1142
    | (have r₁ := eq1142
       have r₂ := eq1413
       grind)
    | exact resolve eq1142 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq1413
  have eq1425 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq1422
  have eq1426 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1425
  have eq1429 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1419
    | exact resolve eq1419 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1443 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1429 eq1368
    | (have r₁ := eq1368
       have r₂ := eq1429
       grind)
    | exact resolve eq1368 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368
  have eq1444 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1443
  have eq1445 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1444
  have eq1462 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1445 eq27
    | exact resolve eq27 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1445 eq175
    | (have r₁ := eq175
       have r₂ := eq1445
       grind)
    | exact resolve eq175 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1445
  have eq1469 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1463
  have eq1472 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1429 eq1462
    | exact resolve eq1462 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1473 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq1472
  have eq1508 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1426 eq41
    | exact resolve eq41 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1426
  have eq1509 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1508
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1508
    | exact resolve eq1508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508
  have eq1511 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1429 eq1509
    | exact resolve eq1509 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429 eq1509
  have eq1548 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1469 eq1511
    | exact resolve eq1511 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1549 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1469 eq90
    | exact resolve eq90 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1469
  have eq1551 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1548
  have eq1562 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1549
    | exact resolve eq1549 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1549
  have eq1563 : x = (M.op x y) := by
    first
    | (have r₁ := eq1551
       have r₂ := eq1473
       grind)
    | exact resolve eq1551 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473 eq1551
  have eq1568 : y = (k x y) := by
    first
    | (have r₁ := eq1562
       have r₂ := eq174
       grind)
    | exact resolve eq1562 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1562
  have eq1571 : y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq1568
       have i₂ := eq1563
       grind)
    | exact superpose eq1563 eq1568
    | exact resolve eq1568 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq1575 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1563
       grind)
    | exact superpose eq1563 eq22
    | exact resolve eq22 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1563
  have eq2058 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1575 eq20
    | exact resolve eq20 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1575
  have eq2152 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1571 eq37
    | exact resolve eq37 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1571
  have eq2155 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2152
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2152
    | exact resolve eq2152 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2152
  have eq2157 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2058 eq2155
    | exact resolve eq2155 eq2058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2175 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2157 eq1163
    | exact resolve eq1163 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq2182 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2175
  have eq2198 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2182 eq1143
    | (have r₁ := eq1143
       have r₂ := eq2182
       grind)
    | exact resolve eq1143 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq2201 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2182
  have eq2202 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2198
  have eq2203 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2202
       have r₂ := eq2201
       grind)
    | exact resolve eq2202 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2206 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2157 eq2203
    | exact resolve eq2203 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157 eq2203
  have eq2207 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2206
       have r₂ := eq2201
       grind)
    | exact resolve eq2206 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201 eq2206
  have eq2211 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2207 eq27
    | exact resolve eq27 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2207
  have eq2220 : False := by grind
  exact eq2220

/-- `Equation3874`: `x ◇ x = (x ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pyy_pyx_Equation3874 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
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
  have eq77 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
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
  clear eq48
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
  clear eq52 eq2925
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
  have eq4531 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq77 eq3005
    | exact resolve eq3005 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4535 : (τ (M.op (M.op x y) (M.op x y))) = (k (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq2929 eq3005
    | exact resolve eq3005 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq4569 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (k (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3005 eq4531
    | exact resolve eq4531 eq3005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005 eq4531
  have eq4691 : (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) ∨ (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) ∨ (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq4535 eq14
    | (have j0 := eq14 (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq14 eq4535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4535
  have eq4693 : (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by grind
  clear eq4691
  have eq4712 : ∀ X0 : G, (τ (M.op (M.op x y) (M.op x y))) ≠ (τ (M.op (M.op x y) (M.op x y))) ∨ (k X0 (τ (M.op (M.op x y) (M.op x y)))) = (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4693 eq12
    | (have j0 := eq12 X0 (τ (M.op (M.op x y) (M.op x y)))
       grind)
    | (have r₁ := eq12 X0 (τ (M.op (M.op x y) (M.op x y)))
       have r₂ := eq4693
       grind)
    | exact resolve eq12 eq4693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4721 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4693 eq9
    | exact resolve eq9 eq4693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693
  have eq4723 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) (M.op x y)))) = (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq4712 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4712
  have eq4756 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4723 eq4569
    | exact resolve eq4569 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4569
  have eq4801 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4723 eq4756
    | exact resolve eq4756 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723 eq4756
  have eq4821 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq4721 eq4801
    | exact resolve eq4801 eq4721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4721 eq4801
  have eq4900 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq4821 X0
       grind)
    | exact superpose eq4821 eq11
    | exact resolve eq11 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4989 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4900 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4900
    | exact resolve eq4900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4900
  have eq6163 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
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
  have eq6178 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ≠ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
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
  have eq6181 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) X1) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3))) := by
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
  clear eq1138
  have eq6200 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6181 X0 X1 X2 X3
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6181
    | exact resolve eq6181 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6181
  have eq6203 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6178 X0 X1
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6178
    | (have j0 := eq6178 X0 X1
       grind)
    | exact resolve eq6178 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq6178
  have eq6229 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6200 X0 X1 X2 X3
       have i₂ := eq6163 X0 X0
       grind)
    | exact superpose eq6163 eq6200
    | exact resolve eq6200 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6200
  have eq6232 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq6203 X0 X1
       grind)
    | (have r₁ := eq6203 X0 X1
       have r₂ := eq6163 X0 X0
       grind)
    | exact resolve eq6203 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203
  have eq6240 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6232 X0 X1
       have i₂ := eq6163 X0 X0
       grind)
    | exact superpose eq6163 eq6232
    | exact resolve eq6232 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163 eq6232
  have eq6589 : ∀ X0 X1 : G, (k (τ X0) (τ (M.op X1 X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 (M.op X1 X1)
       have i₂ := eq6240 X1 X0
       grind)
    | exact superpose eq6240 eq130
    | exact resolve eq130 eq6240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq6600 : ∀ X0 X1 : G, (k (τ X0) (M.op (τ X1) (τ X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6589 X0 X1
       have i₂ := eq4821 X1
       grind)
    | exact superpose eq4821 eq6589
    | exact resolve eq6589 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6589
  have eq6638 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X1) (τ X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6600 X0 X1
       have i₂ := eq6240 (τ X1) (τ X0)
       grind)
    | exact superpose eq6240 eq6600
    | exact resolve eq6600 eq6240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6600
  have eq7181 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq7372 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq7181 (M.op x (M.op (M.op x x) x))
       have i₂ := eq2648 x x x x x
       grind)
    | exact superpose eq2648 eq7181
    | exact resolve eq7181 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq7181
  have eq7412 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7372 X0
       have i₂ := eq2899 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq2899 eq7372
    | exact resolve eq7372 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7372
  have eq7430 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2899 X0 X1
       have i₂ := eq7412 X0
       grind)
    | exact superpose eq7412 eq2899
    | exact resolve eq2899 eq7412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899 eq7412
  have eq7479 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7430 (M.op X0 (M.op (M.op X1 x) x)) (M.op X0 (M.op (M.op X1 x) x))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq7430
    | exact resolve eq7430 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7575 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6229 X0 X1 X2 X3
       have i₂ := eq7479 X0 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq7479 eq6229
    | exact resolve eq6229 eq7479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6229 eq7479
  have eq10193 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op (M.op X0 X0) X1) X4) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X4 X5) X6)) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq7575 (M.op X0 (M.op (M.op X1 x) x)) X1 x x
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq7575
    | exact resolve eq7575 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq10339 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 (M.op X1 X2) (M.op X0 X0)
       have i₂ := eq7575 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq7575 eq77
    | exact resolve eq77 eq7575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7575
  have eq10391 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10339 X0 X1 X2
       have i₂ := eq7430 X0 X0
       grind)
    | exact superpose eq7430 eq10339
    | exact resolve eq10339 eq7430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7430 eq10339
  have eq10501 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10391 X0 x x
       have i₂ := eq10193 X0 x x x sF0
       grind)
    | exact superpose eq10193 eq10391
    | exact resolve eq10391 eq10193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10391
  have eq10651 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X1 X2)) X1 X2
       have i₂ := eq10501 X0 (M.op X1 X2)
       grind)
    | exact superpose eq10501 eq9
    | exact resolve eq9 eq10501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10501
  have eq10681 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10651 X0 X1 X2
       have i₂ := eq10193 X0 (M.op X1 X2) X0 X0 (M.op X1 X2)
       grind)
    | exact superpose eq10193 eq10651
    | exact resolve eq10651 eq10193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10193 eq10651
  have eq10723 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10681 X0 X1 X2
       have i₂ := eq2638 X0 (M.op X1 X2)
       grind)
    | exact superpose eq2638 eq10681
    | exact resolve eq10681 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638 eq10681
  have eq14701 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (τ (M.op X0 X0)) (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6638 (M.op X0 X0) X1
       have i₂ := eq10723 X0 X1 X1
       grind)
    | exact superpose eq10723 eq6638
    | exact resolve eq6638 eq10723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6638
  have eq14749 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14701 X0 X1
       have i₂ := eq4821 X0
       grind)
    | exact superpose eq4821 eq14701
    | exact resolve eq14701 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14701
  have eq14775 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (M.op (τ X0) (τ X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14749 X0 X1
       have i₂ := eq10723 (τ X0) (τ X1) (τ X1)
       grind)
    | exact superpose eq10723 eq14749
    | exact resolve eq14749 eq10723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10723 eq14749
  have eq15762 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) X1)
       have i₂ := eq14775 X0 X1
       grind)
    | exact superpose eq14775 eq11
    | exact resolve eq11 eq14775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14775
  have eq15996 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) X1) = (σ (M.op (M.op X0 X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15762 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15762
    | exact resolve eq15762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15762
  have eq17133 : ∀ X0 X1 : G, (M.op (M.op (σ X1) (σ X1)) (σ X0)) = (σ (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15996 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15996
    | exact resolve eq15996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15996
  have eq21176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq21214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21176
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21176
    | exact resolve eq21176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21176
  have eq21217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq21214
    | exact resolve eq21214 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21214
  have eq21218 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21217
       have r₂ := eq27
       grind)
    | exact resolve eq21217 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21217
  have eq21234 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21218 eq4821
    | exact resolve eq4821 eq21218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21218
  have eq21271 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39 eq21234
    | exact resolve eq21234 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq21234
  have eq21272 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq21271
  have eq21294 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21272 eq4821
    | exact resolve eq4821 eq21272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821 eq21272
  have eq21329 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq21294
    | exact resolve eq21294 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq21294
  have eq21330 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq21329
  have eq21350 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4989 y
       have i₂ := eq21330
       grind)
    | exact superpose eq21330 eq4989
    | exact resolve eq4989 eq21330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21354 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6240 y x
       have i₂ := eq21330
       grind)
    | exact superpose eq21330 eq6240
    | exact resolve eq6240 eq21330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21330
  have eq21386 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21350
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21350
    | exact resolve eq21350 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21350
  have eq21411 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21386 eq6240
    | exact resolve eq6240 eq21386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6240 eq21386
  have eq22403 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21411 eq63
    | exact resolve eq63 eq21411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq21411
  have eq22474 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq22403
    | exact resolve eq22403 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22403
  have eq22495 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22474
       have i₂ := eq21354 x
       grind)
    | exact superpose eq21354 eq22474
    | exact resolve eq22474 eq21354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21354 eq22474
  have eq22525 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq22495
  have eq22530 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22525
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22525
    | exact resolve eq22525 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22525
  have eq22535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq22530
    | exact resolve eq22530 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22530
  have eq22538 : x = (M.op x x) := by
    first
    | (have r₁ := eq22535
       have r₂ := eq27
       grind)
    | exact resolve eq22535 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22535
  have eq22651 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4989 x
       have i₂ := eq22538
       grind)
    | exact superpose eq22538 eq4989
    | exact resolve eq4989 eq22538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989
  have eq22672 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17133 X0 x
       have i₂ := eq22538
       grind)
    | exact superpose eq22538 eq17133
    | exact resolve eq17133 eq22538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17133 eq22538
  have eq22685 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22672 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22672
    | (have j0 := eq22672 X0
       grind)
    | exact resolve eq22672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22672
  have eq23526 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22651
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22651
    | exact resolve eq22651 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22651
  have eq24078 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq23526 eq22685
    | exact resolve eq22685 eq23526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22685 eq23526
  have eq32991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24078 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24078
    | (have j0 := eq24078 y
       grind)
    | exact resolve eq24078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24078
  have eq33063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32991
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32991
    | exact resolve eq32991 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq32991
  have eq33079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq33063
    | exact resolve eq33063 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq33063
  have eq33087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq33079
    | exact resolve eq33079 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq33079
  have eq33091 : False := by grind
  exact eq33091

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_x_y_pyx_pxx_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq91 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq15
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq91
    | exact resolve eq91 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq91
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq102
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       have j1 := eq120 X0 X1
       grind)
    | (have r₁ := eq140 X0 X1
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq140 X0 (σ (M.op X0 X0))
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq140 (M.op X0 X0) (σ X0)
       have r₂ := eq120 X0 X1
       grind)
    | exact resolve eq140 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq140
  have eq169 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq147
    | exact resolve eq147 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq147 X1 (σ X0)
       grind)
    | exact superpose eq147 eq15
    | (have j1 := eq147 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq182 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq169 (τ X1) X0
       grind)
    | exact superpose eq169 eq18
    | (have j1 := eq169 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq169
  have eq271 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
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
  have eq297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq271 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq271
    | (have j0 := eq271 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq883 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq173 x y
       grind)
    | exact superpose eq173 eq16
    | (have j1 := eq173 x y
       grind)
    | exact resolve eq16 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq897 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq883
       have i₂ := eq297 y x
       grind)
    | exact superpose eq297 eq883
    | (have j1 := eq297 (σ x) (σ y)
       grind)
    | (have r₁ := eq883
       have r₂ := eq297 y x
       grind)
    | (have r₁ := eq883
       have r₂ := eq297 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq883
       have r₂ := eq297 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq883 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq883
  have eq898 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq897
  have eq900 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq16
    | exact resolve eq16 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq901 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq900
       have r₂ := eq102 x
       grind)
    | exact resolve eq900 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq902 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq901
       grind)
    | exact superpose eq901 eq16
    | exact resolve eq16 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq901
       grind)
    | exact superpose eq901 eq10
    | exact resolve eq10 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq945 : x = y := by
    first
    | (have i₁ := eq903
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq903
    | exact resolve eq903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq946 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq902
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq902
    | exact resolve eq902 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq902
  have eq947 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq946
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq946
    | exact resolve eq946 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq946
  have eq948 : False := by grind
  exact eq948

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_x_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq429 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq12
    | (have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq445 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq429 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq456 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq445
    | (have j0 := eq445 X0 X1
       grind)
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq457 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq549 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq457
    | exact resolve eq457 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq457 x y
       grind)
    | exact superpose eq457 eq16
    | (have j1 := eq457 x y
       grind)
    | exact resolve eq16 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq580 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq549
    | (have j0 := eq549 X0 X1
       grind)
    | exact resolve eq549 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq549
  have eq723 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq580
    | exact resolve eq580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq776 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq723 (τ X0) X1
       grind)
    | exact superpose eq723 eq18
    | (have j1 := eq723 (τ X0) X1
       grind)
    | exact resolve eq18 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq723
  have eq1085 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq776 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq776
    | exact resolve eq776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq1135 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1085 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1085
    | (have j0 := eq1085 X0 X1
       grind)
    | exact resolve eq1085 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1272 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq556
       have i₂ := eq1135 x y
       grind)
    | exact superpose eq1135 eq556
    | (have j1 := eq1135 (σ x) (σ y)
       grind)
    | (have r₁ := eq556
       have r₂ := eq1135 x y
       grind)
    | exact resolve eq556 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq1273 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1272
  have eq1317 : y ≠ y ∨ y = (k y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1273
       grind)
    | exact superpose eq1273 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1273
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1273
       grind)
    | exact resolve eq13 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : y = (M.op y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1317
  have eq3110 : y ≠ (M.op x y) ∨ y = (k y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1321
       grind)
    | exact superpose eq1321 eq12
    | exact resolve eq12 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq3122 : y ≠ (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3110
  have eq3125 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3122
       have r₂ := eq1273
       grind)
    | exact resolve eq3122 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273 eq3122
  have eq3130 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq570 x y
       have i₂ := eq3125
       grind)
    | exact superpose eq3125 eq570
    | (have j0 := eq570 x y
       grind)
    | exact resolve eq570 eq3125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq3125
  have eq3151 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3130
  have eq3152 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3151
  have eq3256 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3152
       grind)
    | exact superpose eq3152 eq16
    | exact resolve eq16 eq3152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3263 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3152
       grind)
    | exact superpose eq3152 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3152
       grind)
    | exact resolve eq13 eq3152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3274 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq3263
  have eq3285 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq3274
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3274
    | exact resolve eq3274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq3522 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3285
       grind)
    | exact superpose eq3285 eq12
    | exact resolve eq12 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq3553 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq3522
       have r₂ := eq3152
       grind)
    | exact resolve eq3522 eq3152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152 eq3522
  have eq3578 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq3553
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3553
    | exact resolve eq3553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq3579 : (σ y) = (σ (k y x)) := by grind
  clear eq3578
  have eq3700 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1135 x y
       have i₂ := eq3579
       grind)
    | exact superpose eq3579 eq1135
    | (have j0 := eq1135 x y
       grind)
    | exact resolve eq1135 eq3579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq3579
  have eq3772 : y = (M.op x y) := by
    first
    | (have r₁ := eq3700
       have r₂ := eq3256
       grind)
    | exact resolve eq3700 eq3256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3700
  have eq3961 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3256
       have i₂ := eq3772
       grind)
    | exact superpose eq3772 eq3256
    | exact resolve eq3256 eq3772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256 eq3772
  have eq3978 : False := by grind
  exact eq3978

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_x_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq442 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq457 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq460 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq453
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq453 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq471 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq457 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq457 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq457 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq457 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq474 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq460
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq460
    | exact resolve eq460 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq491 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq471 X1 (τ X0)
       grind)
    | exact superpose eq471 eq18
    | (have j1 := eq471 X1 (τ X0)
       grind)
    | exact resolve eq18 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq508 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq471 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq491 X1 (τ X0)
       grind)
    | exact superpose eq491 eq17
    | (have j1 := eq491 X1 (τ X0)
       grind)
    | exact resolve eq17 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq491
  have eq953 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq948 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq948
    | (have j0 := eq948 X0 X1
       grind)
    | exact resolve eq948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq972 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq953
    | (have j0 := eq953 X0 X1
       grind)
    | exact resolve eq953 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq978 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq972 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq972
    | (have j0 := eq972 X0 X1
       grind)
    | exact resolve eq972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1052 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq978 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq978
    | (have j0 := eq978 X1 (σ X0)
       grind)
    | exact resolve eq978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1417 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X0 X0
       have i₂ := eq471 X0 (σ X0)
       grind)
    | exact superpose eq471 eq1052
    | (have j0 := eq1052 X0 X1
       have j1 := eq471 X1 (σ X0)
       grind)
    | exact resolve eq1052 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq1052
  have eq1466 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1417 X0 X1
       have j1 := eq508 X1 (σ X0)
       grind)
    | (have r₁ := eq1417 X0 X0
       have r₂ := eq508 X0 (σ X0)
       grind)
    | exact resolve eq1417 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq1417
  have eq1684 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1466 X1 (σ X0)
       grind)
    | exact superpose eq1466 eq28
    | (have j1 := eq1466 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1466
  have eq1696 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1684 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1684
    | (have j0 := eq1684 X0 X1
       grind)
    | exact resolve eq1684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1715 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1696 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1696
    | (have j0 := eq1696 X0 X1
       grind)
    | exact resolve eq1696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq1727 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1715 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1715
    | (have j0 := eq1715 X0 X1
       grind)
    | exact resolve eq1715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq1841 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1727 y x
       grind)
    | exact superpose eq1727 eq16
    | (have j1 := eq1727 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1727 y x
       grind)
    | exact resolve eq16 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1864 : y = (k y x) := by grind
  clear eq1841
  have eq2177 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq474
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq474
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq474 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2178 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq2177
  have eq2180 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2178
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2178 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq2181 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2180
       have i₂ := eq1864
       grind)
    | exact superpose eq1864 eq2180
    | exact resolve eq2180 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2182 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2181
       have i₂ := eq1864
       grind)
    | exact superpose eq1864 eq2181
    | exact resolve eq2181 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181
  have eq2183 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq474
       have i₂ := eq2182
       grind)
    | exact superpose eq2182 eq474
    | exact resolve eq474 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq2182
  have eq2193 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2183
  have eq2194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2193
       have i₂ := eq1864
       grind)
    | exact superpose eq1864 eq2193
    | exact resolve eq2193 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2195 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2194
  have eq2203 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2195
       grind)
    | exact superpose eq2195 eq16
    | exact resolve eq16 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2236 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2203
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq2203
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq2203 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2237 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq2236
  have eq2240 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2237
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2237 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237
  have eq2241 : y = (M.op x y) := by
    first
    | (have i₁ := eq2240
       have i₂ := eq1864
       grind)
    | exact superpose eq1864 eq2240
    | exact resolve eq2240 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864 eq2240
  have eq2242 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2203
       have i₂ := eq2241
       grind)
    | exact superpose eq2241 eq2203
    | exact resolve eq2203 eq2241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203 eq2241
  have eq2254 : False := by grind
  exact eq2254

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq263 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq263 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq263 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq264 (σ X0)
       grind)
    | exact superpose eq264 eq15
    | exact resolve eq15 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq275
    | exact resolve eq275 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq275
  have eq339 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq401 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq400 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq421 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq401 (σ X1) (σ X0)
       grind)
    | exact superpose eq401 eq15
    | (have j1 := eq401 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq401 (τ X1) X0
       grind)
    | exact superpose eq401 eq17
    | (have j1 := eq401 (τ X1) X0
       grind)
    | exact resolve eq17 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq401
  have eq438 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq421
    | (have j0 := eq421 X0 X1
       grind)
    | exact resolve eq421 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq421
  have eq449 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq429
    | exact resolve eq429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq449
    | (have j0 := eq449 X0 X1
       grind)
    | exact resolve eq449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq838 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq438 x y
       grind)
    | exact superpose eq438 eq16
    | (have j1 := eq438 x y
       grind)
    | exact resolve eq16 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq438 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq872 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq838
       have i₂ := eq487 y x
       grind)
    | exact superpose eq487 eq838
    | (have j1 := eq487 y x
       grind)
    | (have r₁ := eq838
       have r₂ := eq487 y x
       grind)
    | exact resolve eq838 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq873 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq872
  have eq878 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq873
       grind)
    | exact resolve eq13 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : y = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq878
  have eq7341 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq881
       grind)
    | exact superpose eq881 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq881
       grind)
    | exact resolve eq12 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq7344 : (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7341
  have eq28827 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq855 x y
       have i₂ := eq7344
       grind)
    | exact superpose eq7344 eq855
    | (have j0 := eq855 x y
       grind)
    | exact resolve eq855 eq7344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7344
  have eq28873 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq28827
  have eq28874 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq28873
  have eq28886 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28874
       grind)
    | exact superpose eq28874 eq16
    | exact resolve eq16 eq28874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28874
  have eq28927 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28886
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq28886
    | exact resolve eq28886 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq28886
  have eq28939 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq28927
  have eq28953 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq855 x y
       have i₂ := eq28939
       grind)
    | exact superpose eq28939 eq855
    | (have j0 := eq855 x y
       grind)
    | exact resolve eq855 eq28939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq28939
  have eq28998 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq28953
  have eq28999 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq28998
  have eq29011 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28999
       grind)
    | exact superpose eq28999 eq16
    | exact resolve eq16 eq28999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29012 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq339 x (σ y)
       have i₂ := eq28999
       grind)
    | exact superpose eq28999 eq339
    | (have j0 := eq339 x (σ y)
       grind)
    | (have r₁ := eq339 x (σ y)
       have r₂ := eq28999
       grind)
    | exact resolve eq339 eq28999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq29042 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq29012
  have eq29049 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq29042
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq29042
    | exact resolve eq29042 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29042
  have eq35627 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq29049
       grind)
    | exact superpose eq29049 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq29049
       grind)
    | exact resolve eq12 eq29049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29049
  have eq35641 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq35627
  have eq35654 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq35641
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq35641
    | exact resolve eq35641 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35641
  have eq35684 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq35654
       have i₂ := eq28999
       grind)
    | exact superpose eq28999 eq35654
    | exact resolve eq35654 eq28999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28999 eq35654
  have eq35685 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq35684
  have eq35719 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq487 y x
       have i₂ := eq35685
       grind)
    | exact superpose eq35685 eq487
    | (have j0 := eq487 y x
       grind)
    | exact resolve eq487 eq35685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq35685
  have eq35869 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq35719
       have r₂ := eq29011
       grind)
    | exact resolve eq35719 eq29011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35719
  have eq36028 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29011
       have i₂ := eq35869
       grind)
    | exact superpose eq35869 eq29011
    | exact resolve eq29011 eq35869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29011 eq35869
  have eq36042 : False := by grind
  exact eq36042

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq274 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq379 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq274 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq274 X0 X1
       grind)
    | exact resolve eq13 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq274 (σ x) (σ y)
       grind)
    | exact superpose eq274 eq16
    | (have j1 := eq274 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq389 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq384
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq384
    | exact resolve eq384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq391 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq388 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq388 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq405 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq391 X1 (τ X0)
       grind)
    | exact superpose eq391 eq18
    | (have j1 := eq391 X1 (τ X0)
       grind)
    | exact resolve eq18 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq422 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq405 X1 (τ X0)
       grind)
    | exact superpose eq405 eq17
    | (have j1 := eq405 X1 (τ X0)
       grind)
    | exact resolve eq17 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq405
  have eq716 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq711
    | (have j0 := eq711 X0 X1
       grind)
    | exact resolve eq711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq734 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq737 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq794 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq737 X0 X1
       have i₂ := eq391 X0 X1
       grind)
    | exact superpose eq391 eq737
    | (have j0 := eq737 X1 X0
       have j1 := eq391 X1 X0
       grind)
    | exact resolve eq737 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq737
  have eq854 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq794 X0 X1
       have j1 := eq422 X1 X0
       grind)
    | (have r₁ := eq794 X1 X0
       have r₂ := eq422 X0 X1
       grind)
    | exact resolve eq794 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq794
  have eq906 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq854 X1 (σ X0)
       grind)
    | exact superpose eq854 eq28
    | (have j1 := eq854 X1 (σ X0)
       grind)
    | exact resolve eq28 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq854
  have eq922 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq906 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq906
    | (have j0 := eq906 X0 X1
       grind)
    | exact resolve eq906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq948 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq922
    | (have j0 := eq922 X0 X1
       grind)
    | exact resolve eq922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1189 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq948 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq948
    | exact resolve eq948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1189 x y
       grind)
    | exact superpose eq1189 eq16
    | (have j1 := eq1189 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1189 x y
       grind)
    | exact resolve eq16 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1266 : y = (k y x) := by grind
  clear eq1251
  have eq2176 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq389
       have i₂ := eq274 x y
       grind)
    | exact superpose eq274 eq389
    | (have j1 := eq274 x y
       grind)
    | exact resolve eq389 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2179 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2176
  have eq2182 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2179
       have i₂ := eq1266
       grind)
    | exact superpose eq1266 eq2179
    | exact resolve eq2179 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq2184 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2182
       have i₂ := eq1266
       grind)
    | exact superpose eq1266 eq2182
    | exact resolve eq2182 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182
  have eq2186 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq389
       have i₂ := eq2184
       grind)
    | exact superpose eq2184 eq389
    | exact resolve eq389 eq2184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq2184
  have eq2198 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2186
  have eq2199 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2198
       have i₂ := eq1266
       grind)
    | exact superpose eq1266 eq2198
    | exact resolve eq2198 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2200 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2199
  have eq2203 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2200
       grind)
    | exact superpose eq2200 eq16
    | exact resolve eq16 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2239 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2203
       have i₂ := eq274 x y
       grind)
    | exact superpose eq274 eq2203
    | (have j1 := eq274 x y
       grind)
    | exact resolve eq2203 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq2242 : (M.op x y) = (k y x) := by grind
  clear eq2239
  have eq2246 : y = (M.op x y) := by
    first
    | (have i₁ := eq2242
       have i₂ := eq1266
       grind)
    | exact superpose eq1266 eq2242
    | exact resolve eq2242 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq2242
  have eq2248 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2203
       have i₂ := eq2246
       grind)
    | exact superpose eq2246 eq2203
    | exact resolve eq2203 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203 eq2246
  have eq2262 : False := by grind
  exact eq2262
