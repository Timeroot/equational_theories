import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxx_pyy_pxy_pyy_pyy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19
    | exact resolve eq19 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq42
    | exact resolve eq42 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq66 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq46
    | exact resolve eq46 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq40 (τ X0)
       grind)
    | exact superpose eq40 eq66
    | exact resolve eq66 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq66
  have eq81 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq97 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq84
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq84
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq98 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq97
  have eq109 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq98
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq98
       grind)
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69 (σ y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq69
    | exact resolve eq69 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq122 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq112
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq112
    | exact resolve eq112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq131 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq122
       grind)
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq122
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq122
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq132 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq131
  have eq138 : (τ (M.op (σ y) (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq46 (σ y) (σ x)
       have i₂ := eq132
       grind)
    | exact superpose eq132 eq46
    | exact resolve eq46 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq144 : (τ (M.op (σ y) (σ y))) = (k (τ (σ x)) y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq138
    | exact resolve eq138 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq151 : (τ (M.op (σ y) (σ y))) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq144
    | exact resolve eq144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq152 : (M.op (τ (σ y)) (τ (σ y))) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq151
       have i₂ := eq69 (σ y)
       grind)
    | exact superpose eq69 eq151
    | exact resolve eq151 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq153 : (M.op y y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq152
    | exact resolve eq152 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq154 : (M.op y y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq153
       have r₂ := eq11 x y
       grind)
    | exact resolve eq153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq158 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq154
       grind)
    | exact superpose eq154 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq161 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq158
  have eq171 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq161
       grind)
    | exact superpose eq161 eq10
    | exact resolve eq10 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq175 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq171
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq171
    | exact resolve eq171 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq185 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq175
       grind)
    | exact superpose eq175 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq175
       grind)
    | exact resolve eq11 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq189 : (M.op y y) = (k x y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq188
  have eq192 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq185
    | exact resolve eq185 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq196 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq189
       grind)
    | exact superpose eq189 eq15
    | exact resolve eq15 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq199 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq196
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq196
    | exact resolve eq196 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq244 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 (σ x) (σ y)
       have i₂ := eq199
       grind)
    | exact superpose eq199 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq247 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq244
  have eq252 : (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq247
       have r₂ := eq192
       grind)
    | exact resolve eq247 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq247
  have eq274 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op y y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq252
       grind)
    | exact superpose eq252 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq252
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq252
       grind)
    | exact resolve eq13 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : (M.op x y) ≠ (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq252
  have eq384 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq274 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq385 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq384
  have eq391 : (M.op x x) = (k x y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq385
       have r₂ := eq281
       grind)
    | exact resolve eq385 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq385
  have eq400 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq391
       grind)
    | exact superpose eq391 eq15
    | exact resolve eq15 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq407 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq400
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq400
    | exact resolve eq400 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq411 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq109 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq412 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq411
  have eq424 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14 (σ x) (σ y)
       have i₂ := eq407
       grind)
    | exact superpose eq407 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq424
  have eq466 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq427
       grind)
    | exact superpose eq427 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq427
       grind)
    | exact resolve eq11 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq467 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq466
  have eq487 : (k (τ (σ x)) (τ (σ y))) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq46 (σ y) (σ x)
       have i₂ := eq412
       grind)
    | exact superpose eq412 eq46
    | exact resolve eq46 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq412
  have eq497 : (k (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq487
       have i₂ := eq69 (σ x)
       grind)
    | exact superpose eq69 eq487
    | exact resolve eq487 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq500 : (M.op x x) = (k x (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq497
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq497
    | exact resolve eq497 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq501 : (M.op x x) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq500
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq500
    | exact resolve eq500 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq502 : (M.op x x) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq501
       have r₂ := eq13 x y
       grind)
    | exact resolve eq501 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq507 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq407
       have i₂ := eq467
       grind)
    | exact superpose eq467 eq407
    | exact resolve eq407 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq467
  have eq514 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq507
  have eq528 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq514
       grind)
    | exact superpose eq514 eq43
    | exact resolve eq43 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq536 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq528
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq528
    | exact resolve eq528 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq537 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq536
  have eq545 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ y)
       have i₂ := eq537
       grind)
    | exact superpose eq537 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq537
       grind)
    | exact resolve eq13 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  have eq567 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq502
       grind)
    | exact superpose eq502 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq570 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq567
  have eq578 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq570
       have r₂ := eq551
       grind)
    | exact resolve eq570 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq641 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq578
       grind)
    | exact superpose eq578 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq578
       grind)
    | exact resolve eq11 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq642 : (M.op y y) = (k x y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq641
  have eq663 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq642
       grind)
    | exact superpose eq642 eq15
    | exact resolve eq15 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq670 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq663
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq663
    | exact resolve eq663 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq1068 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq545 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq1069 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1068
  have eq1076 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq1069
       have r₂ := eq551
       grind)
    | exact resolve eq1069 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq1069
  have eq1086 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq670
       have i₂ := eq1076
       grind)
    | exact superpose eq1076 eq670
    | exact resolve eq670 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq1076
  have eq1091 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1086
  have eq1164 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq1091
       grind)
    | exact superpose eq1091 eq43
    | exact resolve eq43 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1235 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1164
       grind)
    | exact superpose eq1164 eq16
    | exact resolve eq16 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1244 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq1235
       have r₂ := eq537
       grind)
    | exact resolve eq1235 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq1235
  have eq1256 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq1244
       grind)
    | exact superpose eq1244 eq43
    | exact resolve eq43 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1268 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1256
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq1256
    | exact resolve eq1256 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1269 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1268
  have eq1273 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq1269
       grind)
    | exact superpose eq1269 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1269
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1269
       grind)
    | exact resolve eq12 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq69 (σ y)
       have i₂ := eq1269
       grind)
    | exact superpose eq1269 eq69
    | exact resolve eq69 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1279 : (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq1276
       have i₂ := eq69 (σ x)
       grind)
    | exact superpose eq69 eq1276
    | exact resolve eq1276 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1276
  have eq1283 : (M.op x x) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq1279
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1279
    | exact resolve eq1279 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1284 : (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1283
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1283
    | exact resolve eq1283 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1288 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) ≠ (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1284
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1284
       grind)
    | exact resolve eq12 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1365 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq1273 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1426 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) ≠ (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1288 X0
       grind)
    | exact superpose eq1288 eq15
    | (have j1 := eq1288 X0
       grind)
    | exact resolve eq15 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1572 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1426 x
       grind)
    | exact superpose eq1426 eq16
    | (have j1 := eq1426 x
       grind)
    | exact resolve eq16 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1574 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1572
  have eq1578 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1574
       have i₂ := eq1365
       grind)
    | exact superpose eq1365 eq1574
    | (have r₁ := eq1574
       have r₂ := eq1365
       grind)
    | exact resolve eq1574 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1581 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1578
  have eq1585 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq1581
       grind)
    | exact superpose eq1581 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1581
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1581
       grind)
    | exact resolve eq11 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1586 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1585
  have eq1587 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1586
       have i₂ := eq1269
       grind)
    | exact superpose eq1269 eq1586
    | exact resolve eq1586 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269 eq1586
  have eq1590 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1574
       have i₂ := eq1587
       grind)
    | exact superpose eq1587 eq1574
    | exact resolve eq1574 eq1587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574 eq1587
  have eq1597 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1590
  have eq1602 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1597
       have r₂ := eq1581
       grind)
    | exact resolve eq1597 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581 eq1597
  have eq1604 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1602
       grind)
    | exact superpose eq1602 eq16
    | exact resolve eq16 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1605 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1604
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq1604
    | exact resolve eq1604 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1610 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1602
       grind)
    | exact superpose eq1602 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1602
       grind)
    | exact resolve eq11 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1611 : (M.op y y) = (k x y) := by grind
  clear eq1610
  have eq1614 : (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq1611
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq1611
    | exact resolve eq1611 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284 eq1611
  have eq1626 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq1614
       grind)
    | exact superpose eq1614 eq15
    | exact resolve eq15 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq1633 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1626
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq1626
    | exact resolve eq1626 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1626
  have eq1636 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1365
       have i₂ := eq1633
       grind)
    | exact superpose eq1633 eq1365
    | exact resolve eq1365 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365 eq1633
  have eq1637 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1636
  have eq1639 : False := by grind
  exact eq1639

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_pyy_pxy_pyx_pyy_pxx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
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
    | (have j0 := eq9 X0
       grind)
    | exact resolve eq9 eq18
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
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq21
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
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq30
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
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq63 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq11
    | (have j0 := eq11 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq11 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq64
       have i₂ := eq65 sF4
       grind)
    | exact superpose eq65 eq64
    | exact resolve eq64 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq67 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq63
       have i₂ := eq65 (τ sF4)
       grind)
    | exact superpose eq65 eq63
    | exact resolve eq63 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq69 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq65 sF5
       grind)
    | exact superpose eq65 eq66
    | exact resolve eq66 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq65 (τ sF5)
       grind)
    | exact superpose eq65 eq67
    | exact resolve eq67 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq114 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq131 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq137 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq137 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq137 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq154 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq65 sF5
       grind)
    | exact superpose eq65 eq133
    | exact resolve eq133 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq156 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq131
       have i₂ := eq65 (τ sF5)
       grind)
    | exact superpose eq65 eq131
    | exact resolve eq131 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq163 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq151
    | (have j0 := eq151 X0 X1
       grind)
    | (have r₁ := eq151 X0 X0
       have r₂ := eq65 X0
       grind)
    | exact resolve eq151 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq166 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq154
       have i₂ := eq65 sF4
       grind)
    | exact superpose eq65 eq154
    | exact resolve eq154 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq168 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq156
       have i₂ := eq65 (τ sF4)
       grind)
    | exact superpose eq65 eq156
    | exact resolve eq156 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq174 : ∀ X0 X1 : G, (k X0 X1) = (k X1 X1) ∨ (k X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq163
    | (have j0 := eq163 X0 X1
       grind)
    | exact resolve eq163 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq181 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq174
    | (have j0 := eq174 X0 X1
       grind)
    | exact resolve eq174 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq247 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq11
    | (have j0 := eq11 X0 X1
       grind)
    | exact resolve eq11 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | (have r₁ := eq248 X0 X0
       have r₂ := eq65 X0
       grind)
    | exact resolve eq248 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq250 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq247 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq247
    | (have j0 := eq247 X0 X1
       grind)
    | (have r₁ := eq247 X0 X0
       have r₂ := eq65 X0
       grind)
    | exact resolve eq247 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq251 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ (k X1 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | (have r₁ := eq250 X0 X0
       have r₂ := eq65 X0
       grind)
    | exact resolve eq250 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq402 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq166 eq33
    | exact resolve eq33 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  have eq404 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  have eq463 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq168 eq15
    | exact resolve eq15 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq464 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq463
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq463
    | exact resolve eq463 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq465 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq26 eq464
    | exact resolve eq464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq471 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq465 eq15
    | exact resolve eq15 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq471
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq471
    | exact resolve eq471 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq473 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq472
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq472
    | exact resolve eq472 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq474 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq26 eq473
    | exact resolve eq473 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq475 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq474 eq70
    | (have r₁ := eq70
       have r₂ := eq474
       grind)
    | exact resolve eq70 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq474 eq15
    | exact resolve eq15 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq479 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by grind
  clear eq475
  have eq480 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq478
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq478
    | exact resolve eq478 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq481 : (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq480
    | exact resolve eq480 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq489 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq481 eq13
    | (have j0 := eq13 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq13 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq494 : (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq489
       have r₂ := eq42
       grind)
    | exact resolve eq489 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq498 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq494
       have i₂ := eq65 (τ sF5)
       grind)
    | exact superpose eq65 eq494
    | exact resolve eq494 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq502 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq42 eq498
    | exact resolve eq498 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq504 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq502
       have i₂ := eq65 (τ sF4)
       grind)
    | exact superpose eq65 eq502
    | exact resolve eq502 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq505 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq42 eq504
    | exact resolve eq504 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq523 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq479 eq15
    | exact resolve eq15 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq526 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq523
       have i₂ := eq15 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq15 eq523
    | exact resolve eq523 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq528 : (k (σ y) (σ y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq526
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq526
    | exact resolve eq526 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq529 : (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq528
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq528
    | exact resolve eq528 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq533 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq529 eq13
    | (have j0 := eq13 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq13 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq538 : (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq533
       have r₂ := eq42
       grind)
    | exact resolve eq533 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq542 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq538
       have i₂ := eq65 (τ sF5)
       grind)
    | exact superpose eq65 eq538
    | exact resolve eq538 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq546 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq42 eq542
    | exact resolve eq542 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq548 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq546
       have i₂ := eq65 (τ sF4)
       grind)
    | exact superpose eq65 eq546
    | exact resolve eq546 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq549 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq42 eq548
    | exact resolve eq548 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq596 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq251
    | (have j0 := eq251 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq251 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq251
    | (have j0 := eq251 (σ y) (σ x)
       grind)
    | exact resolve eq251 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq876 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq166 eq600
    | (have r₁ := eq600
       have r₂ := eq166
       grind)
    | exact resolve eq600 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq877 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq876
  have eq878 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq877
       have r₂ := eq403
       grind)
    | exact resolve eq877 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq877
  have eq1072 : (k (τ (σ x)) (τ (σ y))) = (τ (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq878 eq114
    | exact resolve eq114 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq114 sF4 sF4
       grind)
    | exact superpose eq114 eq1072
    | exact resolve eq1072 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1085 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1079 eq465
    | exact resolve eq465 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq1090 : (k (τ (σ x)) (τ (σ x))) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1079 eq181
    | (have j0 := eq181 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq181 (τ (σ x)) (τ (σ y))
       have r₂ := eq1079
       grind)
    | exact resolve eq181 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1091 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1090
  have eq1094 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1085
  have eq1098 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq1091
    | exact resolve eq1091 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1102 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1094
       have r₂ := eq402
       grind)
    | exact resolve eq1094 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1104 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq1098
    | exact resolve eq1098 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1951 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1104
  have eq1962 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1951
       have r₂ := eq1102
       grind)
    | exact resolve eq1951 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq1951
  have eq1983 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1962 eq15
    | exact resolve eq15 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq2002 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1983
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1983
    | exact resolve eq1983 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq2005 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq2002
    | exact resolve eq2002 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2006 : (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2005
       have r₂ := eq402
       grind)
    | exact resolve eq2005 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2010 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2006 eq13
    | (have j0 := eq13 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2006
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2006
       grind)
    | exact resolve eq13 eq2006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2015 : (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2010
       have r₂ := eq42
       grind)
    | exact resolve eq2010 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2019 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2015
       have i₂ := eq65 (τ sF5)
       grind)
    | exact superpose eq65 eq2015
    | exact resolve eq2015 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq2023 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq2019
    | exact resolve eq2019 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2026 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2023
       have i₂ := eq65 (τ sF4)
       grind)
    | exact superpose eq65 eq2023
    | exact resolve eq2023 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023
  have eq2028 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq2026
    | exact resolve eq2026 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2026
  have eq4898 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq505 eq15
    | exact resolve eq15 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq4926 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4898
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq4898
    | exact resolve eq4898 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4898
  have eq4927 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4926
    | exact resolve eq4926 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4926
  have eq4928 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq4927
  have eq4941 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4928 eq15
    | exact resolve eq15 eq4928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4928
  have eq4956 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4941
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq4941
    | exact resolve eq4941 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4941
  have eq4966 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4956
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq4956
    | exact resolve eq4956 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956
  have eq4967 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4966
    | exact resolve eq4966 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4966
  have eq4968 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq4967
  have eq4974 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4968 eq15
    | exact resolve eq15 eq4968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4968
  have eq4989 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4974
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq4974
    | exact resolve eq4974 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4974
  have eq4990 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4989
    | exact resolve eq4989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989
  have eq4991 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq4990
  have eq5006 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4991 eq36
    | exact resolve eq36 eq4991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5014 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4991 eq402
    | (have r₁ := eq402
       have r₂ := eq4991
       grind)
    | exact resolve eq402 eq4991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5036 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  have eq5037 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  have eq5038 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq5014
  have eq5064 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq5006
       have i₂ := eq114 sF5 sF5
       grind)
    | exact superpose eq114 eq5006
    | exact resolve eq5006 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5006
  have eq5116 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5064 eq596
    | (have r₁ := eq596
       have r₂ := eq5064
       grind)
    | exact resolve eq596 eq5064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5140 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq5116
  have eq9260 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5038 eq69
    | (have r₁ := eq69
       have r₂ := eq5038
       grind)
    | exact resolve eq69 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038
  have eq9266 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq9260
       have r₂ := eq69
       grind)
    | exact resolve eq9260 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9260
  have eq9268 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq9266
       have r₂ := eq5036
       grind)
    | exact resolve eq9266 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9266
  have eq9271 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq878 eq9268
    | (have r₁ := eq9268
       have r₂ := eq878
       grind)
    | exact resolve eq9268 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq9272 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq9271
  have eq9273 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq9272
  have eq28391 : (k (σ (τ (σ x))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5140 eq15
    | exact resolve eq15 eq5140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5140
  have eq28423 : (k (σ (τ (σ x))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28391
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq28391
    | exact resolve eq28391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28391
  have eq28424 : (k (σ x) (σ x)) = (k (σ x) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28423
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq28423
    | exact resolve eq28423 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28423
  have eq28425 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28424
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq28424
    | exact resolve eq28424 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28424
  have eq28459 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq28425 eq15
    | exact resolve eq15 eq28425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28425
  have eq28477 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28459
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq28459
    | exact resolve eq28459 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28459
  have eq28478 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq28477
    | exact resolve eq28477 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28477
  have eq28479 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq28478
  have eq28500 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28479 eq9268
    | (have r₁ := eq9268
       have r₂ := eq28479
       grind)
    | exact resolve eq9268 eq28479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9268
  have eq28519 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq28500
  have eq28520 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq28519
  have eq28600 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28520 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28520
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28520
       grind)
    | exact resolve eq13 eq28520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28601 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28520 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28520
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28520
       grind)
    | exact resolve eq13 eq28520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28604 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28520 eq249
    | (have j0 := eq249 (σ y) (σ x)
       grind)
    | exact resolve eq249 eq28520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28520
  have eq28608 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq28601
       have r₂ := eq32
       grind)
    | exact resolve eq28601 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28601
  have eq28609 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq28600
       have r₂ := eq32
       grind)
    | exact resolve eq28600 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28600
  have eq28612 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq28608
       have i₂ := eq65 sF5
       grind)
    | exact superpose eq65 eq28608
    | exact resolve eq28608 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28608
  have eq28613 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq28609
       have i₂ := eq65 sF4
       grind)
    | exact superpose eq65 eq28609
    | exact resolve eq28609 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28609
  have eq28616 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq28612
    | exact resolve eq28612 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28612
  have eq28617 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq28613
       have i₂ := eq65 sF5
       grind)
    | exact superpose eq65 eq28613
    | exact resolve eq28613 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28613
  have eq28619 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq28616
       have i₂ := eq65 sF4
       grind)
    | exact superpose eq65 eq28616
    | exact resolve eq28616 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28616
  have eq28620 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq28617
    | exact resolve eq28617 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28617
  have eq28621 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq28619
    | exact resolve eq28619 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28619
  have eq29936 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq549 eq15
    | exact resolve eq15 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq29976 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq29936
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq29936
    | exact resolve eq29936 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29936
  have eq29982 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq29976
    | exact resolve eq29976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29976
  have eq29983 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq29982
  have eq31138 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28620 eq33
    | exact resolve eq33 eq28620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31145 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28620 eq9273
    | exact resolve eq9273 eq28620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9273 eq28620
  have eq31159 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq31145
  have eq31171 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq31159
       have r₂ := eq69
       grind)
    | exact resolve eq31159 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31159
  have eq31176 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq31138
       have r₂ := eq4991
       grind)
    | exact resolve eq31138 eq4991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4991 eq31138
  have eq31177 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq31171
       have r₂ := eq5036
       grind)
    | exact resolve eq31171 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31171
  have eq31181 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq31177
       have r₂ := eq5037
       grind)
    | exact resolve eq31177 eq5037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5037 eq31177
  have eq31192 : (k (σ x) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq31176 eq69
    | (have r₁ := eq69
       have r₂ := eq31176
       grind)
    | exact resolve eq69 eq31176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31176
  have eq31227 : (k (σ x) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq31192
       have r₂ := eq69
       grind)
    | exact resolve eq31192 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31192
  have eq31229 : (k (σ x) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq31227
       have r₂ := eq5036
       grind)
    | exact resolve eq31227 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5036 eq31227
  have eq31882 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq31181 eq249
    | (have j0 := eq249 (σ y) (σ x)
       grind)
    | (have r₁ := eq249 (σ y) (σ x)
       have r₂ := eq31181
       grind)
    | exact resolve eq249 eq31181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31181
  have eq31883 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq31882
  have eq31887 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq31883
       have r₂ := eq31229
       grind)
    | exact resolve eq31883 eq31229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31883
  have eq31909 : (k (σ y) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq31887 eq28604
    | exact resolve eq28604 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28604
  have eq31910 : (k (σ y) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq31909
  have eq31925 : (k (σ y) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq31910
       have r₂ := eq31229
       grind)
    | exact resolve eq31910 eq31229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31910
  have eq32246 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq31887 eq28621
    | exact resolve eq28621 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28621 eq31887
  have eq32278 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq32246
  have eq32291 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq32278
       have r₂ := eq31925
       grind)
    | exact resolve eq32278 eq31925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31925 eq32278
  have eq32298 : (k (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq32291
       have r₂ := eq31229
       grind)
    | exact resolve eq32291 eq31229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32291
  have eq32320 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32298 eq31229
    | exact resolve eq31229 eq32298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31229 eq32298
  have eq32335 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq32320
  have eq32357 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq32335
       have r₂ := eq28479
       grind)
    | exact resolve eq32335 eq28479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28479 eq32335
  have eq199297 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq29983 eq15
    | exact resolve eq15 eq29983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29983
  have eq199354 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq199297
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq199297
    | exact resolve eq199297 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199297
  have eq199396 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq199354
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq199354
    | exact resolve eq199354 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199354
  have eq199436 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq199396
    | exact resolve eq199396 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199396
  have eq199437 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq199436
  have eq199438 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq199437 eq70
    | (have r₁ := eq70
       have r₂ := eq199437
       grind)
    | exact resolve eq70 eq199437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199437
  have eq199533 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq199438
  have eq204072 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2028 eq15
    | exact resolve eq15 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq204128 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq204072
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq204072
    | exact resolve eq204072 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204072
  have eq204129 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq204128
    | exact resolve eq204128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204128
  have eq204130 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq204129
       have r₂ := eq402
       grind)
    | exact resolve eq204129 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq204129
  have eq452610 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq204130 eq1079
    | exact resolve eq1079 eq204130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq204130
  have eq452936 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq452610
  have eq452947 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq452936 eq70
    | (have r₁ := eq70
       have r₂ := eq452936
       grind)
    | exact resolve eq70 eq452936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452936
  have eq453293 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq452947
  have eq454159 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq453293 eq15
    | exact resolve eq15 eq453293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453293
  have eq454215 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq454159
       have i₂ := eq15 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq15 eq454159
    | exact resolve eq454159 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454159
  have eq454220 : (k (σ y) (σ y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq454215
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq454215
    | exact resolve eq454215 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454215
  have eq454223 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq454220
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq454220
    | exact resolve eq454220 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454220
  have eq454224 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq454223
       have r₂ := eq69
       grind)
    | exact resolve eq454223 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454223
  have eq454226 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq454224 eq404
    | (have r₁ := eq404
       have r₂ := eq454224
       grind)
    | exact resolve eq404 eq454224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq454224
  have eq454315 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq454226
  have eq454316 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq454315
  have eq454390 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq454316 eq33
    | exact resolve eq33 eq454316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454393 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq454316 eq600
    | exact resolve eq600 eq454316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454402 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq454316
  have eq454403 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq454393
  have eq454406 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq454403
       have r₂ := eq454402
       grind)
    | exact resolve eq454403 eq454402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454402 eq454403
  have eq477942 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq199533 eq15
    | exact resolve eq15 eq199533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199533
  have eq478046 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq477942
       have i₂ := eq15 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq15 eq477942
    | exact resolve eq477942 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477942
  have eq478049 : (k (σ y) (σ y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq478046
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq478046
    | exact resolve eq478046 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478046
  have eq478050 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq478049
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq478049
    | exact resolve eq478049 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478049
  have eq478051 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq478050
  have eq478099 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq478051 eq454406
    | (have r₁ := eq454406
       have r₂ := eq478051
       grind)
    | exact resolve eq454406 eq478051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454406
  have eq478133 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq478099
  have eq478182 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq478133
       have r₂ := eq454390
       grind)
    | exact resolve eq478133 eq454390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478133
  have eq478358 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq478182 eq33
    | exact resolve eq33 eq478182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478359 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq478182 eq69
    | (have r₁ := eq69
       have r₂ := eq478182
       grind)
    | exact resolve eq69 eq478182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478182
  have eq478369 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq478359
  have eq478557 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq478369 eq114
    | exact resolve eq114 eq478369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478369
  have eq478604 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq478557
       have i₂ := eq114 sF5 sF4
       grind)
    | exact superpose eq114 eq478557
    | exact resolve eq478557 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478557
  have eq480853 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5064 eq478604
    | exact resolve eq478604 eq5064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5064 eq478604
  have eq481005 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq480853
       have r₂ := eq478358
       grind)
    | exact resolve eq480853 eq478358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478358 eq480853
  have eq483394 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq481005 eq15
    | exact resolve eq15 eq481005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481005
  have eq483609 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq483394
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq483394
    | exact resolve eq483394 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483394
  have eq483616 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq483609
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq483609
    | exact resolve eq483609 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483609
  have eq483622 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq483616
    | exact resolve eq483616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483616
  have eq483623 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq483622
  have eq483773 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq483623 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq483623
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq483623
       grind)
    | exact resolve eq13 eq483623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483623
  have eq483792 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq483773
       have r₂ := eq32
       grind)
    | exact resolve eq483773 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483773
  have eq483796 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq483792
       have i₂ := eq65 sF5
       grind)
    | exact superpose eq65 eq483792
    | exact resolve eq483792 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483792
  have eq483800 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq483796
    | exact resolve eq483796 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483796
  have eq483803 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq483800
       have i₂ := eq65 sF4
       grind)
    | exact superpose eq65 eq483800
    | exact resolve eq483800 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483800
  have eq483805 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq483803
    | exact resolve eq483803 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483803
  have eq492268 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq483805
  have eq492287 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq492268
       have r₂ := eq478051
       grind)
    | exact resolve eq492268 eq478051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492268
  have eq492505 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq492287 eq600
    | exact resolve eq600 eq492287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492517 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq492287
  have eq492528 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq492505
  have eq492540 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq492528
       have r₂ := eq492517
       grind)
    | exact resolve eq492528 eq492517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492517 eq492528
  have eq492541 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq492540
       have r₂ := eq478051
       grind)
    | exact resolve eq492540 eq478051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478051 eq492540
  have eq492557 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq492541 eq33
    | exact resolve eq33 eq492541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492541
  have eq492588 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq492557
       have r₂ := eq32357
       grind)
    | exact resolve eq492557 eq32357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492557
  have eq492808 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq492588 eq36
    | exact resolve eq36 eq492588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492947 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq492588 eq32357
    | exact resolve eq32357 eq492588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32357
  have eq493334 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq492588
  have eq493519 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq492947
       have r₂ := eq493334
       grind)
    | exact resolve eq492947 eq493334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492947
  have eq493631 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq492808
       have i₂ := eq114 sF5 sF5
       grind)
    | exact superpose eq114 eq492808
    | exact resolve eq492808 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492808
  have eq493906 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq493519 eq114
    | exact resolve eq114 eq493519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493519
  have eq493986 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq493906
       have i₂ := eq114 sF4 sF4
       grind)
    | exact superpose eq114 eq493906
    | exact resolve eq493906 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493906
  have eq496077 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq493986 eq493631
    | exact resolve eq493631 eq493986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493631 eq493986
  have eq496096 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq496077
  have eq496289 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq496096 eq70
    | (have r₁ := eq70
       have r₂ := eq496096
       grind)
    | exact resolve eq70 eq496096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496096
  have eq496329 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq496289
  have eq506255 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq496329 eq15
    | exact resolve eq15 eq496329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496329
  have eq506329 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq506255
       have i₂ := eq15 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq15 eq506255
    | exact resolve eq506255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506255
  have eq506330 : (k (σ y) (σ y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq506329
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq506329
    | exact resolve eq506329 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506329
  have eq506331 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq506330
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq506330
    | exact resolve eq506330 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506330
  have eq506332 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq506331
       have r₂ := eq493334
       grind)
    | exact resolve eq506331 eq493334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493334 eq506331
  have eq506435 : (M.op x y) = (τ (k (σ x) (σ y))) := by
    first
    | exact superpose eq506332 eq36
    | exact resolve eq36 eq506332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq507311 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq506332 eq454390
    | (have r₁ := eq454390
       have r₂ := eq506332
       grind)
    | exact resolve eq454390 eq506332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454390
  have eq507350 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq507311
  have eq507541 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq506435
       have i₂ := eq114 sF5 sF4
       grind)
    | exact superpose eq114 eq506435
    | exact resolve eq506435 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506435
  have eq507838 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) := by
    first
    | exact superpose eq507541 eq15
    | exact resolve eq15 eq507541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507864 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) := by
    first
    | (have i₁ := eq507838
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq507838
    | exact resolve eq507838 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507838
  have eq507865 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq507864
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq507864
    | exact resolve eq507864 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507864
  have eq508207 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq507350 eq33
    | exact resolve eq33 eq507350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508208 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq507350 eq69
    | (have r₁ := eq69
       have r₂ := eq507350
       grind)
    | exact resolve eq69 eq507350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507350
  have eq508217 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq508208
  have eq508218 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq506332 eq508207
    | exact resolve eq508207 eq506332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508207
  have eq508888 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq508217 eq114
    | exact resolve eq114 eq508217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508217
  have eq508941 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq508888
       have i₂ := eq114 sF5 sF4
       grind)
    | exact superpose eq114 eq508888
    | exact resolve eq508888 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508888
  have eq508944 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq507541 eq508941
    | exact resolve eq508941 eq507541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508941
  have eq509007 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq508944 eq596
    | (have r₁ := eq596
       have r₂ := eq508944
       grind)
    | exact resolve eq596 eq508944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508944
  have eq509102 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq509007
  have eq509108 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq507541 eq509102
    | exact resolve eq509102 eq507541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509102
  have eq509109 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq509108
  have eq509114 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq509109 eq15
    | exact resolve eq15 eq509109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509109
  have eq509149 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq509114
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq509114
    | exact resolve eq509114 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509114
  have eq509151 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq509149
    | exact resolve eq509149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509149
  have eq509152 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq506332 eq509151
    | exact resolve eq509151 eq506332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509151
  have eq509153 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq509152
       have r₂ := eq508218
       grind)
    | exact resolve eq509152 eq508218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508218 eq509152
  have eq509267 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq509153 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq509153
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq509153
       grind)
    | exact resolve eq13 eq509153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509268 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq509153 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq509153
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq509153
       grind)
    | exact resolve eq13 eq509153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509271 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq509153 eq249
    | (have j0 := eq249 (σ y) (σ x)
       grind)
    | exact resolve eq249 eq509153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq509153
  have eq509273 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq509268
       have r₂ := eq32
       grind)
    | exact resolve eq509268 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509268
  have eq509274 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq509267
       have r₂ := eq32
       grind)
    | exact resolve eq509267 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509267
  have eq509277 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq509273
       have i₂ := eq65 sF5
       grind)
    | exact superpose eq65 eq509273
    | exact resolve eq509273 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509273
  have eq509278 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq509274
       have i₂ := eq65 sF4
       grind)
    | exact superpose eq65 eq509274
    | exact resolve eq509274 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509274
  have eq509281 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq509277
    | exact resolve eq509277 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509277
  have eq509282 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq509278
       have i₂ := eq65 sF5
       grind)
    | exact superpose eq65 eq509278
    | exact resolve eq509278 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509278
  have eq509285 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq509281
       have i₂ := eq65 sF4
       grind)
    | exact superpose eq65 eq509281
    | exact resolve eq509281 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq509281
  have eq509286 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq509282
    | exact resolve eq509282 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509282
  have eq509287 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq509285
    | exact resolve eq509285 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq509285
  have eq509570 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq509286 eq33
    | exact resolve eq33 eq509286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509572 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq509286 eq600
    | (have r₁ := eq600
       have r₂ := eq509286
       grind)
    | exact resolve eq600 eq509286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq509582 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq509286
  have eq509584 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq509572
  have eq509590 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq509584
       have r₂ := eq509582
       grind)
    | exact resolve eq509584 eq509582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509582 eq509584
  have eq509592 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq506332 eq509570
    | exact resolve eq509570 eq506332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509570
  have eq509641 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq509287 eq69
    | (have r₁ := eq69
       have r₂ := eq509287
       grind)
    | exact resolve eq69 eq509287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509651 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  have eq509661 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq509641
       have r₂ := eq69
       grind)
    | exact resolve eq509641 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509641
  have eq512324 : (k (τ (σ x)) (τ (σ y))) = (τ (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq509590 eq114
    | exact resolve eq114 eq509590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509590
  have eq512337 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq512324
       have i₂ := eq114 sF4 sF4
       grind)
    | exact superpose eq114 eq512324
    | exact resolve eq512324 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512324
  have eq512378 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq507541 eq512337
    | exact resolve eq512337 eq507541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512337
  have eq512698 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq512378 eq70
    | (have r₁ := eq70
       have r₂ := eq512378
       grind)
    | exact resolve eq70 eq512378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq512378
  have eq512733 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq512698
  have eq512736 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq507541 eq512733
    | exact resolve eq512733 eq507541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512733
  have eq513115 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq512736 eq15
    | exact resolve eq15 eq512736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512736
  have eq513149 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq513115
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq513115
    | exact resolve eq513115 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513115
  have eq513150 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq513149
    | exact resolve eq513149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq513149
  have eq513151 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq506332 eq513150
    | exact resolve eq513150 eq506332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513150
  have eq513152 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq513151
       have r₂ := eq69
       grind)
    | exact resolve eq513151 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513151
  have eq513264 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq513152 eq509592
    | (have r₁ := eq509592
       have r₂ := eq513152
       grind)
    | exact resolve eq509592 eq513152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509592 eq513152
  have eq513304 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq513264
  have eq513305 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq513304
  have eq513327 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq509287 eq513305
    | exact resolve eq513305 eq509287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513345 : (k (σ y) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq513305 eq509271
    | exact resolve eq509271 eq513305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509271
  have eq513348 : (k (σ x) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq513305
  have eq513352 : (k (σ y) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq513345
       have r₂ := eq513348
       grind)
    | exact resolve eq513345 eq513348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513345 eq513348
  have eq513364 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq513327
       have r₂ := eq509651
       grind)
    | exact resolve eq513327 eq509651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509651 eq513327
  have eq513372 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq513364
       have r₂ := eq513352
       grind)
    | exact resolve eq513364 eq513352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513352 eq513364
  have eq513501 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq509287 eq513372
    | exact resolve eq513372 eq509287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509287
  have eq513503 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq513372 eq33
    | exact resolve eq33 eq513372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513504 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq513372 eq69
    | (have r₁ := eq69
       have r₂ := eq513372
       grind)
    | exact resolve eq69 eq513372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513372
  have eq513533 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq513504
       have r₂ := eq69
       grind)
    | exact resolve eq513504 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513504
  have eq513534 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq513503
       have r₂ := eq506332
       grind)
    | exact resolve eq513503 eq506332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513503
  have eq513536 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq513501
       have r₂ := eq509661
       grind)
    | exact resolve eq513501 eq509661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509661 eq513501
  have eq513542 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq513536
       have r₂ := eq69
       grind)
    | exact resolve eq513536 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq513536
  have eq513543 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq513534 eq513542
    | exact resolve eq513542 eq513534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513542
  have eq513544 : (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq513543
       have r₂ := eq513533
       grind)
    | exact resolve eq513543 eq513533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513533 eq513543
  have eq513565 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq513534 eq33
    | exact resolve eq33 eq513534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq513534
  have eq513585 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq506332 eq513565
    | exact resolve eq513565 eq506332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506332 eq513565
  have eq513760 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ y))) := by
    first
    | exact superpose eq513544 eq114
    | exact resolve eq114 eq513544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513544
  have eq513801 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq513760
       have i₂ := eq114 sF5 sF4
       grind)
    | exact superpose eq114 eq513760
    | exact resolve eq513760 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq513760
  have eq513803 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq507541 eq513801
    | exact resolve eq513801 eq507541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513801
  have eq513893 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq513803 eq596
    | (have r₁ := eq596
       have r₂ := eq513803
       grind)
    | exact resolve eq596 eq513803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq513803
  have eq513980 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) := by grind
  clear eq513893
  have eq513984 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq507541 eq513980
    | exact resolve eq513980 eq507541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507541 eq513980
  have eq513985 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by grind
  clear eq513984
  have eq514045 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq513985 eq15
    | exact resolve eq15 eq513985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513985
  have eq514081 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq514045
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq514045
    | exact resolve eq514045 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq514045
  have eq514085 : (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq514081 eq507865
    | exact resolve eq507865 eq514081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507865 eq514081
  have eq514273 : False := by grind
  exact eq514273

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = X then X else if X = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_x_x_y_pxy_x_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq94 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq100 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq94 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq94 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq94 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq94
  have eq325 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X1) X0
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ X1) X0
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq550 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq325 X0 (σ X1)
       grind)
    | exact superpose eq325 eq29
    | (have j1 := eq325 (M.op X0 (σ X1)) X0
       grind)
    | exact resolve eq29 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq551 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq325 X0 (τ X1)
       grind)
    | exact superpose eq325 eq19
    | (have j1 := eq325 (M.op X0 (τ X1)) X0
       grind)
    | exact resolve eq19 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3353 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq5082 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X1)
       have i₂ := eq550 X0 X1
       grind)
    | exact superpose eq550 eq12
    | (have j0 := eq12 X0 (σ X1)
       have j1 := eq550 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq550 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq550 (M.op (σ X1) X1) X1
       grind)
    | exact resolve eq12 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5083 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (σ X1)
       have i₂ := eq550 X0 X1
       grind)
    | exact superpose eq550 eq11
    | (have j1 := eq550 X0 X1
       grind)
    | exact resolve eq11 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq5087 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5082 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5082
  have eq5094 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5087 X0 X1
       have j1 := eq5083 X0 X1
       grind)
    | (have r₁ := eq5087 X0 X1
       have r₂ := eq5083 X0 X1
       grind)
    | (have r₁ := eq5087 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq5083 (σ X1) X1
       grind)
    | exact resolve eq5087 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5083 eq5087
  have eq5149 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq551
    | exact resolve eq551 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq5171 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5149 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5149
    | (have j0 := eq5149 X0 X1
       grind)
    | exact resolve eq5149 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq5177 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq5171 X0 X1
       grind)
    | exact superpose eq5171 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq5171 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq5171 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq5171 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5171 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq5171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5178 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq5171 X0 X1
       grind)
    | exact superpose eq5171 eq11
    | (have j1 := eq5171 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5171 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5171 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq5171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171
  have eq5182 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177
  have eq5189 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5182 X0 X1
       have j1 := eq5178 X0 X1
       grind)
    | (have r₁ := eq5182 X0 X1
       have r₂ := eq5178 X0 X1
       grind)
    | (have r₁ := eq5182 (M.op X0 X0) X0
       have r₂ := eq5178 X0 X1
       grind)
    | (have r₁ := eq5182 X0 (M.op X0 X0)
       have r₂ := eq5178 X0 X1
       grind)
    | exact resolve eq5182 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178 eq5182
  have eq6067 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq5094 (σ X0) X1
       grind)
    | exact superpose eq5094 eq38
    | (have j1 := eq5094 (σ X1) X0
       grind)
    | exact resolve eq38 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5094
  have eq6148 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6067 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq6067
    | (have j0 := eq6067 X0 X1
       grind)
    | exact resolve eq6067 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6067
  have eq6181 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6148 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6148
    | (have j0 := eq6148 X0 X1
       grind)
    | exact resolve eq6148 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6148
  have eq6191 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6181 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6181
    | (have j0 := eq6181 X0 X1
       grind)
    | exact resolve eq6181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6181
  have eq6712 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq6191 X0 X1
       grind)
    | exact superpose eq6191 eq10
    | (have j1 := eq6191 X0 X1
       grind)
    | exact resolve eq10 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191
  have eq8131 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6712 x y
       grind)
    | exact superpose eq6712 eq16
    | (have j1 := eq6712 x y
       grind)
    | exact resolve eq16 eq6712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712
  have eq8251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8131
       have i₂ := eq325 x y
       grind)
    | exact superpose eq325 eq8131
    | (have j1 := eq325 x y
       grind)
    | (have r₁ := eq8131
       have r₂ := eq325 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8131
       have r₂ := eq325 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8131 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq8253 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq8131
       have i₂ := eq5189 x y
       grind)
    | exact superpose eq5189 eq8131
    | (have j1 := eq5189 x y
       grind)
    | (have r₁ := eq8131
       have r₂ := eq5189 x y
       grind)
    | (have r₁ := eq8131
       have r₂ := eq5189 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8131
       have r₂ := eq5189 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8131 eq5189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5189 eq8131
  have eq8254 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8253
  have eq8255 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq8254
  have eq8258 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8251
  have eq8259 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8258
  have eq8262 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8255
       grind)
    | exact superpose eq8255 eq16
    | exact resolve eq16 eq8255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8255
  have eq8263 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8262
       have r₂ := eq23 x
       grind)
    | exact resolve eq8262 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262
  have eq8404 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3353 x y
       have i₂ := eq8263
       grind)
    | exact superpose eq8263 eq3353
    | (have j0 := eq3353 x y
       grind)
    | exact resolve eq3353 eq8263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353 eq8263
  have eq8409 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8404
  have eq8410 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8409
  have eq8421 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8259
       grind)
    | exact superpose eq8259 eq16
    | exact resolve eq16 eq8259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8259
  have eq8422 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8421
       have r₂ := eq23 x
       grind)
    | exact resolve eq8421 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8421
  have eq8564 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8410
       grind)
    | exact superpose eq8410 eq16
    | exact resolve eq16 eq8410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8410
  have eq8669 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8564
       have i₂ := eq8422
       grind)
    | exact superpose eq8422 eq8564
    | exact resolve eq8564 eq8422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422 eq8564
  have eq8674 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq8669
  have eq8675 : (σ x) = (σ y) := by grind
  clear eq8674
  have eq8676 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8675
       grind)
    | exact superpose eq8675 eq16
    | exact resolve eq16 eq8675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8677 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq8675
       grind)
    | exact superpose eq8675 eq9
    | exact resolve eq9 eq8675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8675
  have eq8756 : x = y := by
    first
    | (have i₁ := eq8677
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8677
    | exact resolve eq8677 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8677
  have eq8757 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8676
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq8676
    | exact resolve eq8676 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8676
  have eq8758 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8757
       have i₂ := eq8756
       grind)
    | exact superpose eq8756 eq8757
    | exact resolve eq8757 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8756 eq8757
  have eq8759 : False := by grind
  exact eq8759

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = X then X else if X = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_x_x_y_pxy_x_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq94 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq100 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq94 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq94 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq94 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq94
  have eq325 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X1) X0
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ X1) X0
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq550 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq325 X0 (σ X1)
       grind)
    | exact superpose eq325 eq29
    | (have j1 := eq325 (M.op X0 (σ X1)) X0
       grind)
    | exact resolve eq29 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq551 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq325 X0 (τ X1)
       grind)
    | exact superpose eq325 eq19
    | (have j1 := eq325 (M.op X0 (τ X1)) X0
       grind)
    | exact resolve eq19 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3353 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq5082 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X1)
       have i₂ := eq550 X0 X1
       grind)
    | exact superpose eq550 eq12
    | (have j0 := eq12 X0 (σ X1)
       have j1 := eq550 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq550 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq550 (M.op (σ X1) X1) X1
       grind)
    | exact resolve eq12 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5083 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (σ X1)
       have i₂ := eq550 X0 X1
       grind)
    | exact superpose eq550 eq11
    | (have j1 := eq550 X0 X1
       grind)
    | exact resolve eq11 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq5087 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5082 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5082
  have eq5094 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5087 X0 X1
       have j1 := eq5083 X0 X1
       grind)
    | (have r₁ := eq5087 X0 X1
       have r₂ := eq5083 X0 X1
       grind)
    | (have r₁ := eq5087 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq5083 (σ X1) X1
       grind)
    | exact resolve eq5087 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5083 eq5087
  have eq5149 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq551
    | exact resolve eq551 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq5171 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5149 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5149
    | (have j0 := eq5149 X0 X1
       grind)
    | exact resolve eq5149 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq5177 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq5171 X0 X1
       grind)
    | exact superpose eq5171 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq5171 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq5171 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq5171 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5171 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq5171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5178 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq5171 X0 X1
       grind)
    | exact superpose eq5171 eq11
    | (have j1 := eq5171 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5171 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5171 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq5171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171
  have eq5182 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177
  have eq5189 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5182 X0 X1
       have j1 := eq5178 X0 X1
       grind)
    | (have r₁ := eq5182 X0 X1
       have r₂ := eq5178 X0 X1
       grind)
    | (have r₁ := eq5182 (M.op X0 X0) X0
       have r₂ := eq5178 X0 X1
       grind)
    | (have r₁ := eq5182 X0 (M.op X0 X0)
       have r₂ := eq5178 X0 X1
       grind)
    | exact resolve eq5182 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178 eq5182
  have eq6067 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq5094 (σ X0) X1
       grind)
    | exact superpose eq5094 eq38
    | (have j1 := eq5094 (σ X1) X0
       grind)
    | exact resolve eq38 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5094
  have eq6148 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6067 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq6067
    | (have j0 := eq6067 X0 X1
       grind)
    | exact resolve eq6067 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6067
  have eq6181 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6148 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6148
    | (have j0 := eq6148 X0 X1
       grind)
    | exact resolve eq6148 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6148
  have eq6191 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6181 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6181
    | (have j0 := eq6181 X0 X1
       grind)
    | exact resolve eq6181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6181
  have eq6712 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq6191 X0 X1
       grind)
    | exact superpose eq6191 eq10
    | (have j1 := eq6191 X0 X1
       grind)
    | exact resolve eq10 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191
  have eq8131 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6712 x y
       grind)
    | exact superpose eq6712 eq16
    | (have j1 := eq6712 x y
       grind)
    | exact resolve eq16 eq6712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712
  have eq8251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8131
       have i₂ := eq325 x y
       grind)
    | exact superpose eq325 eq8131
    | (have j1 := eq325 x y
       grind)
    | (have r₁ := eq8131
       have r₂ := eq325 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8131
       have r₂ := eq325 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8131 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq8253 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq8131
       have i₂ := eq5189 x y
       grind)
    | exact superpose eq5189 eq8131
    | (have j1 := eq5189 x y
       grind)
    | (have r₁ := eq8131
       have r₂ := eq5189 x y
       grind)
    | (have r₁ := eq8131
       have r₂ := eq5189 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8131
       have r₂ := eq5189 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8131 eq5189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5189 eq8131
  have eq8254 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8253
  have eq8255 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq8254
  have eq8258 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8251
  have eq8259 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8258
  have eq8262 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8255
       grind)
    | exact superpose eq8255 eq16
    | exact resolve eq16 eq8255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8255
  have eq8263 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8262
       have r₂ := eq23 x
       grind)
    | exact resolve eq8262 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262
  have eq8404 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3353 x y
       have i₂ := eq8263
       grind)
    | exact superpose eq8263 eq3353
    | (have j0 := eq3353 x y
       grind)
    | exact resolve eq3353 eq8263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353 eq8263
  have eq8409 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8404
  have eq8410 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8409
  have eq8421 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8259
       grind)
    | exact superpose eq8259 eq16
    | exact resolve eq16 eq8259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8259
  have eq8422 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8421
       have r₂ := eq23 x
       grind)
    | exact resolve eq8421 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8421
  have eq8564 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8410
       grind)
    | exact superpose eq8410 eq16
    | exact resolve eq16 eq8410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8410
  have eq8669 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8564
       have i₂ := eq8422
       grind)
    | exact superpose eq8422 eq8564
    | exact resolve eq8564 eq8422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422 eq8564
  have eq8674 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq8669
  have eq8675 : (σ x) = (σ y) := by grind
  clear eq8674
  have eq8676 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8675
       grind)
    | exact superpose eq8675 eq16
    | exact resolve eq16 eq8675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8677 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq8675
       grind)
    | exact superpose eq8675 eq9
    | exact resolve eq9 eq8675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8675
  have eq8756 : x = y := by
    first
    | (have i₁ := eq8677
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8677
    | exact resolve eq8677 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8677
  have eq8757 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8676
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq8676
    | exact resolve eq8676 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8676
  have eq8758 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8757
       have i₂ := eq8756
       grind)
    | exact superpose eq8756 eq8757
    | exact resolve eq8757 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8756 eq8757
  have eq8759 : False := by grind
  exact eq8759

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else if X = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_y_x_y_pxx_y_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq51 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq44
    | exact resolve eq44 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq57 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq53 sF2
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq63 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq53 sF2
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq70
    | exact resolve eq70 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq70
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq89 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq3245 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq16644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16644
    | exact resolve eq16644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16644
  have eq16656 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq16645
       have r₂ := eq28
       grind)
    | exact resolve eq16645 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16645
  have eq16660 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16656
    | exact resolve eq16656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16656
  have eq16662 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16660
    | exact resolve eq16660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16660
  have eq16664 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16662 eq52
    | (have r₁ := eq52
       have r₂ := eq16662
       grind)
    | exact resolve eq52 eq16662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16662
  have eq16677 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq16664
  have eq16684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16677 eq90
    | exact resolve eq90 eq16677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16677
  have eq16695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16684
  have eq16698 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16695
       have r₂ := eq28
       grind)
    | exact resolve eq16695 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16695
  have eq16771 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq16698
       grind)
    | exact superpose eq16698 eq51
    | (have r₁ := eq51
       have r₂ := eq16698
       grind)
    | exact resolve eq51 eq16698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16772 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57
       have i₂ := eq16698
       grind)
    | exact superpose eq16698 eq57
    | exact resolve eq57 eq16698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16784 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16771
  have eq16794 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq16772
    | exact resolve eq16772 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16772
  have eq16798 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq16784
       grind)
    | exact superpose eq16784 eq45
    | exact resolve eq45 eq16784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16784
  have eq16822 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq16798
    | exact resolve eq16798 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16822 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq16822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16822
  have eq16964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16963
  have eq16968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq16964
    | exact resolve eq16964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16964
  have eq16979 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16968
       have r₂ := eq28
       grind)
    | exact resolve eq16968 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16968
  have eq16983 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq16979
    | exact resolve eq16979 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16979
  have eq16984 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq16983
  have eq16987 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq16984
    | exact resolve eq16984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16984
  have eq17000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16987 eq16794
    | exact resolve eq16794 eq16987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16794 eq16987
  have eq17004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17000
  have eq17008 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17004
       have r₂ := eq28
       grind)
    | exact resolve eq17004 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17004
  have eq17088 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17008 eq69
    | (have r₁ := eq69
       have r₂ := eq17008
       grind)
    | exact resolve eq69 eq17008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq17089 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17008 eq28
    | exact resolve eq28 eq17008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17008
  have eq17090 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17088
  have eq17241 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17090 eq63
    | exact resolve eq63 eq17090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17242 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17090 eq90
    | exact resolve eq90 eq17090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17090
  have eq17258 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq17242
  have eq17271 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17258
       have r₂ := eq17089
       grind)
    | exact resolve eq17258 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17258
  have eq17272 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq17241
    | exact resolve eq17241 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17241
  have eq17283 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17271 eq52
    | exact resolve eq52 eq17271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17271
  have eq17316 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17283
       have r₂ := eq16698
       grind)
    | exact resolve eq17283 eq16698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16698 eq17283
  have eq17464 : (τ (σ y)) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17316 eq63
    | exact resolve eq63 eq17316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq17465 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17316 eq90
    | exact resolve eq90 eq17316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq17316
  have eq17481 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17465
  have eq17494 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17481
       have r₂ := eq17089
       grind)
    | exact resolve eq17481 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17481
  have eq17495 : y = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq17464
    | exact resolve eq17464 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17464
  have eq17502 : (M.op x y) = (M.op x x) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17495
       have r₂ := eq68
       grind)
    | exact resolve eq17495 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq17495
  have eq17575 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq17494
       grind)
    | exact superpose eq17494 eq51
    | (have r₁ := eq51
       have r₂ := eq17494
       grind)
    | exact resolve eq51 eq17494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17576 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57
       have i₂ := eq17494
       grind)
    | exact superpose eq17494 eq57
    | exact resolve eq57 eq17494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq17494
  have eq17588 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17575
  have eq17598 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17576
    | exact resolve eq17576 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17576
  have eq17729 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17598 eq17272
    | exact resolve eq17272 eq17598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17272 eq17598
  have eq17733 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17729
  have eq17742 : y = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17733
       have r₂ := eq17089
       grind)
    | exact resolve eq17733 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17089 eq17733
  have eq17817 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17588
       have i₂ := eq17742
       grind)
    | exact superpose eq17742 eq17588
    | exact resolve eq17588 eq17742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17588 eq17742
  have eq17823 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq17817
  have eq17939 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq17823 eq30
    | exact resolve eq30 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17823
  have eq18063 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17939
    | exact resolve eq17939 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17939
  have eq18064 : y = (M.op x y) ∨ x = y := by grind
  clear eq18063
  have eq18083 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq18064 eq21
    | exact resolve eq21 eq18064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18216 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18083
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18083
    | exact resolve eq18083 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18083
  have eq278281 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq17502
       grind)
    | exact superpose eq17502 eq51
    | (have r₁ := eq51
       have r₂ := eq17502
       grind)
    | exact resolve eq51 eq17502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq17502
  have eq278303 : (M.op x y) = (k x y) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq278281
  have eq278361 : y ≠ (M.op x y) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq278303
  have eq278375 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq278361
       have r₂ := eq18064
       grind)
    | exact resolve eq278361 eq18064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18064 eq278361
  have eq278500 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq278375
       grind)
    | exact superpose eq278375 eq45
    | exact resolve eq45 eq278375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq278529 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3245 y
       have i₂ := eq278375
       grind)
    | exact superpose eq278375 eq3245
    | (have j0 := eq3245 y
       grind)
    | exact resolve eq3245 eq278375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245 eq278375
  have eq278540 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq278529
  have eq278563 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq278540
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq278540
    | exact resolve eq278540 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278540
  have eq278585 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq278500
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq278500
    | exact resolve eq278500 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278500
  have eq278592 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq278563
    | exact resolve eq278563 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278563
  have eq278607 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq278592
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq278592
    | exact resolve eq278592 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278592
  have eq278608 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq278607
  have eq278620 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq278608
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq278608
    | exact resolve eq278608 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278608
  have eq278631 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq278620
    | exact resolve eq278620 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278620
  have eq299148 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq278631 eq52
    | (have r₁ := eq52
       have r₂ := eq278631
       grind)
    | exact resolve eq52 eq278631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq278631
  have eq299177 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq299148
  have eq300767 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq299177 eq278585
    | exact resolve eq278585 eq299177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278585 eq299177
  have eq300828 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq300767
  have eq300882 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq300828 eq28
    | exact resolve eq28 eq300828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300828
  have eq300884 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq300882
       have r₂ := eq18216
       grind)
    | exact resolve eq300882 eq18216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18216 eq300882
  have eq300888 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq300884 eq30
    | exact resolve eq30 eq300884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq300884
  have eq301719 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq300888
    | exact resolve eq300888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq300888
  have eq301720 : x = y := by grind
  clear eq301719
  have eq301751 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq301720
       grind)
    | exact superpose eq301720 eq19
    | exact resolve eq19 eq301720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq301752 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq301720
       grind)
    | exact superpose eq301720 eq25
    | exact resolve eq25 eq301720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq301720
  have eq302078 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq301752
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq301752
    | exact resolve eq301752 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq301752
  have eq302108 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq302078 eq27
    | exact resolve eq27 eq302078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq302078
  have eq302713 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq302108 eq71
    | exact resolve eq71 eq302108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq302108
  have eq302747 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq302713
       have i₂ := eq301751
       grind)
    | exact superpose eq301751 eq302713
    | exact resolve eq302713 eq301751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301751 eq302713
  have eq302758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq302747 eq15
    | exact resolve eq15 eq302747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302747
  have eq303337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq302758
    | exact resolve eq302758 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq302758
  have eq303485 : False := by grind
  exact eq303485

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else if X = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_y_x_y_pxx_y_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq51 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq44
    | exact resolve eq44 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq57 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq53 sF2
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq63 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq53 sF2
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq70
    | exact resolve eq70 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq70
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq89 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq3245 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq16644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16644
    | exact resolve eq16644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16644
  have eq16656 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq16645
       have r₂ := eq28
       grind)
    | exact resolve eq16645 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16645
  have eq16660 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16656
    | exact resolve eq16656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16656
  have eq16662 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16660
    | exact resolve eq16660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16660
  have eq16664 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16662 eq52
    | (have r₁ := eq52
       have r₂ := eq16662
       grind)
    | exact resolve eq52 eq16662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16662
  have eq16677 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq16664
  have eq16684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16677 eq90
    | exact resolve eq90 eq16677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16677
  have eq16695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16684
  have eq16698 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16695
       have r₂ := eq28
       grind)
    | exact resolve eq16695 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16695
  have eq16771 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq16698
       grind)
    | exact superpose eq16698 eq51
    | (have r₁ := eq51
       have r₂ := eq16698
       grind)
    | exact resolve eq51 eq16698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16772 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57
       have i₂ := eq16698
       grind)
    | exact superpose eq16698 eq57
    | exact resolve eq57 eq16698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16784 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16771
  have eq16794 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq16772
    | exact resolve eq16772 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16772
  have eq16798 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq16784
       grind)
    | exact superpose eq16784 eq45
    | exact resolve eq45 eq16784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16784
  have eq16822 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq16798
    | exact resolve eq16798 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16822 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq16822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16822
  have eq16964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16963
  have eq16968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq16964
    | exact resolve eq16964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16964
  have eq16979 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16968
       have r₂ := eq28
       grind)
    | exact resolve eq16968 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16968
  have eq16983 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq16979
    | exact resolve eq16979 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16979
  have eq16984 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq16983
  have eq16987 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq16984
    | exact resolve eq16984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16984
  have eq17000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16987 eq16794
    | exact resolve eq16794 eq16987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16794 eq16987
  have eq17004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17000
  have eq17008 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17004
       have r₂ := eq28
       grind)
    | exact resolve eq17004 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17004
  have eq17088 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17008 eq69
    | (have r₁ := eq69
       have r₂ := eq17008
       grind)
    | exact resolve eq69 eq17008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq17089 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17008 eq28
    | exact resolve eq28 eq17008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17008
  have eq17090 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17088
  have eq17241 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17090 eq63
    | exact resolve eq63 eq17090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17242 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17090 eq90
    | exact resolve eq90 eq17090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17090
  have eq17258 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq17242
  have eq17271 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17258
       have r₂ := eq17089
       grind)
    | exact resolve eq17258 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17258
  have eq17272 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq17241
    | exact resolve eq17241 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17241
  have eq17283 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17271 eq52
    | exact resolve eq52 eq17271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17271
  have eq17316 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17283
       have r₂ := eq16698
       grind)
    | exact resolve eq17283 eq16698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16698 eq17283
  have eq17464 : (τ (σ y)) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17316 eq63
    | exact resolve eq63 eq17316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq17465 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17316 eq90
    | exact resolve eq90 eq17316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq17316
  have eq17481 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17465
  have eq17494 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17481
       have r₂ := eq17089
       grind)
    | exact resolve eq17481 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17481
  have eq17495 : y = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq17464
    | exact resolve eq17464 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17464
  have eq17502 : (M.op x y) = (M.op x x) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17495
       have r₂ := eq68
       grind)
    | exact resolve eq17495 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq17495
  have eq17575 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq17494
       grind)
    | exact superpose eq17494 eq51
    | (have r₁ := eq51
       have r₂ := eq17494
       grind)
    | exact resolve eq51 eq17494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17576 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57
       have i₂ := eq17494
       grind)
    | exact superpose eq17494 eq57
    | exact resolve eq57 eq17494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq17494
  have eq17588 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17575
  have eq17598 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17576
    | exact resolve eq17576 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17576
  have eq17729 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17598 eq17272
    | exact resolve eq17272 eq17598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17272 eq17598
  have eq17733 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17729
  have eq17742 : y = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17733
       have r₂ := eq17089
       grind)
    | exact resolve eq17733 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17089 eq17733
  have eq17817 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17588
       have i₂ := eq17742
       grind)
    | exact superpose eq17742 eq17588
    | exact resolve eq17588 eq17742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17588 eq17742
  have eq17823 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq17817
  have eq17939 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq17823 eq30
    | exact resolve eq30 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17823
  have eq18063 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17939
    | exact resolve eq17939 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17939
  have eq18064 : y = (M.op x y) ∨ x = y := by grind
  clear eq18063
  have eq18083 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq18064 eq21
    | exact resolve eq21 eq18064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18216 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18083
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18083
    | exact resolve eq18083 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18083
  have eq278281 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq17502
       grind)
    | exact superpose eq17502 eq51
    | (have r₁ := eq51
       have r₂ := eq17502
       grind)
    | exact resolve eq51 eq17502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq17502
  have eq278303 : (M.op x y) = (k x y) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq278281
  have eq278361 : y ≠ (M.op x y) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq278303
  have eq278375 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq278361
       have r₂ := eq18064
       grind)
    | exact resolve eq278361 eq18064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18064 eq278361
  have eq278500 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq278375
       grind)
    | exact superpose eq278375 eq45
    | exact resolve eq45 eq278375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq278529 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3245 y
       have i₂ := eq278375
       grind)
    | exact superpose eq278375 eq3245
    | (have j0 := eq3245 y
       grind)
    | exact resolve eq3245 eq278375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245 eq278375
  have eq278540 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq278529
  have eq278563 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq278540
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq278540
    | exact resolve eq278540 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278540
  have eq278585 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq278500
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq278500
    | exact resolve eq278500 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278500
  have eq278592 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq278563
    | exact resolve eq278563 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278563
  have eq278607 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq278592
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq278592
    | exact resolve eq278592 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278592
  have eq278608 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq278607
  have eq278620 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq278608
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq278608
    | exact resolve eq278608 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278608
  have eq278631 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq278620
    | exact resolve eq278620 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278620
  have eq299148 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq278631 eq52
    | (have r₁ := eq52
       have r₂ := eq278631
       grind)
    | exact resolve eq52 eq278631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq278631
  have eq299177 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq299148
  have eq300767 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq299177 eq278585
    | exact resolve eq278585 eq299177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278585 eq299177
  have eq300828 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq300767
  have eq300882 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq300828 eq28
    | exact resolve eq28 eq300828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300828
  have eq300884 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq300882
       have r₂ := eq18216
       grind)
    | exact resolve eq300882 eq18216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18216 eq300882
  have eq300888 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq300884 eq30
    | exact resolve eq30 eq300884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq300884
  have eq301719 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq300888
    | exact resolve eq300888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq300888
  have eq301720 : x = y := by grind
  clear eq301719
  have eq301751 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq301720
       grind)
    | exact superpose eq301720 eq19
    | exact resolve eq19 eq301720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq301752 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq301720
       grind)
    | exact superpose eq301720 eq25
    | exact resolve eq25 eq301720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq301720
  have eq302078 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq301752
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq301752
    | exact resolve eq301752 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq301752
  have eq302108 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq302078 eq27
    | exact resolve eq27 eq302078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq302078
  have eq302713 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq302108 eq71
    | exact resolve eq71 eq302108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq302108
  have eq302747 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq302713
       have i₂ := eq301751
       grind)
    | exact superpose eq301751 eq302713
    | exact resolve eq302713 eq301751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301751 eq302713
  have eq302758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq302747 eq15
    | exact resolve eq15 eq302747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302747
  have eq303337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq302758
    | exact resolve eq302758 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq302758
  have eq303485 : False := by grind
  exact eq303485

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = Y then Y else if X = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_y_x_y_pxy_y_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq94 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq84
  have eq100 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq94 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq94 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq94 (σ (M.op X0 X0)) X0
       have r₂ := eq46 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq94 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq94
  have eq325 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X1) X0
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ X1) X0
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq562 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq325 (τ X0) X1
       grind)
    | exact superpose eq325 eq18
    | (have j1 := eq325 (τ X0) X1
       grind)
    | exact resolve eq18 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3671 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq5116 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq562 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq562
    | exact resolve eq562 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq5137 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5116 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5116
    | (have j0 := eq5116 X0 X1
       grind)
    | exact resolve eq5116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5116
  have eq5204 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq5137 X0 X1
       grind)
    | exact superpose eq5137 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq5137 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5137 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5137 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq5137 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq5137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5205 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq5137 X0 X1
       grind)
    | exact superpose eq5137 eq11
    | (have j1 := eq5137 X1 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq5137 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5137 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5137 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq5137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5137
  have eq5209 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204
  have eq5216 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5209 X0 X1
       have j1 := eq5205 X0 X1
       grind)
    | (have r₁ := eq5209 (M.op X1 X1) X1
       have r₂ := eq5205 (k X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq5209 X0 X1
       have r₂ := eq5205 X0 X1
       grind)
    | (have r₁ := eq5209 (M.op X1 X1) X1
       have r₂ := eq5205 (M.op X1 X1) X1
       grind)
    | exact resolve eq5209 eq5205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205 eq5209
  have eq5268 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq5216 X1 X0
       grind)
    | exact superpose eq5216 eq9
    | (have j1 := eq5216 X1 X0
       grind)
    | exact resolve eq9 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5323 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5268 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq5268
    | (have j0 := eq5268 X0 X1
       grind)
    | exact resolve eq5268 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5268
  have eq5425 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq5323 (σ X0) X1
       grind)
    | exact superpose eq5323 eq38
    | (have j1 := eq5323 (σ X0) X1
       grind)
    | exact resolve eq38 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5323
  have eq6222 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) X0
       have i₂ := eq5425 X1 (σ X0)
       grind)
    | exact superpose eq5425 eq29
    | (have j1 := eq5425 X1 (σ X0)
       grind)
    | exact resolve eq29 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5425
  have eq6305 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6222 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq6222
    | (have j0 := eq6222 X0 X1
       grind)
    | exact resolve eq6222 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6222
  have eq6343 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6305 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6305
    | (have j0 := eq6305 X0 X1
       grind)
    | exact resolve eq6305 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6305
  have eq6354 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6343 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6343
    | (have j0 := eq6343 X0 X1
       grind)
    | exact resolve eq6343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6343
  have eq6614 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq6354 X1 X0
       grind)
    | exact superpose eq6354 eq10
    | (have j1 := eq6354 X1 X0
       grind)
    | exact resolve eq10 eq6354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6354
  have eq8125 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6614 x y
       grind)
    | exact superpose eq6614 eq16
    | (have j1 := eq6614 x y
       grind)
    | exact resolve eq16 eq6614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq8185 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8125
       have i₂ := eq325 x y
       grind)
    | exact superpose eq325 eq8125
    | (have j1 := eq325 x y
       grind)
    | (have r₁ := eq8125
       have r₂ := eq325 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8125
       have r₂ := eq325 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8125 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq8187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq8125
       have i₂ := eq5216 y x
       grind)
    | exact superpose eq5216 eq8125
    | (have j1 := eq5216 y x
       grind)
    | (have r₁ := eq8125
       have r₂ := eq5216 y x
       grind)
    | (have r₁ := eq8125
       have r₂ := eq5216 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8125
       have r₂ := eq5216 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8125 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216 eq8125
  have eq8188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8187
  have eq8189 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq8188
  have eq8192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8185
  have eq8193 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq8192
  have eq8258 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8189
       grind)
    | exact superpose eq8189 eq16
    | exact resolve eq16 eq8189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8189
  have eq8259 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8258
       have r₂ := eq23 x
       grind)
    | exact resolve eq8258 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8258
  have eq8270 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3671 x y
       have i₂ := eq8259
       grind)
    | exact superpose eq8259 eq3671
    | (have j0 := eq3671 x y
       grind)
    | exact resolve eq3671 eq8259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671 eq8259
  have eq8275 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8270
  have eq8276 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8275
  have eq8370 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8193
       grind)
    | exact superpose eq8193 eq16
    | exact resolve eq16 eq8193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8193
  have eq8371 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8370
       have r₂ := eq23 x
       grind)
    | exact resolve eq8370 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8370
  have eq8465 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8276
       grind)
    | exact superpose eq8276 eq16
    | exact resolve eq16 eq8276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276
  have eq8492 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8465
       have i₂ := eq8371
       grind)
    | exact superpose eq8371 eq8465
    | exact resolve eq8465 eq8371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8371 eq8465
  have eq8497 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq8492
  have eq8498 : (σ x) = (σ y) := by grind
  clear eq8497
  have eq8578 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8498
       grind)
    | exact superpose eq8498 eq16
    | exact resolve eq16 eq8498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8579 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq8498
       grind)
    | exact superpose eq8498 eq9
    | exact resolve eq9 eq8498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8498
  have eq8655 : x = y := by
    first
    | (have i₁ := eq8579
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8579
    | exact resolve eq8579 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8579
  have eq8656 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8578
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq8578
    | exact resolve eq8578 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8578
  have eq8657 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8656
       have i₂ := eq8655
       grind)
    | exact superpose eq8655 eq8656
    | exact resolve eq8656 eq8655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8655 eq8656
  have eq8658 : False := by grind
  exact eq8658

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = Y then Y else if X = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_y_x_y_pxy_y_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq94 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq84
  have eq100 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq94 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq94 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq94 (σ (M.op X0 X0)) X0
       have r₂ := eq46 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq94 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq94
  have eq325 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X1) X0
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ X1) X0
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq562 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq325 (τ X0) X1
       grind)
    | exact superpose eq325 eq18
    | (have j1 := eq325 (τ X0) X1
       grind)
    | exact resolve eq18 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3671 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq5116 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq562 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq562
    | exact resolve eq562 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq5137 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5116 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5116
    | (have j0 := eq5116 X0 X1
       grind)
    | exact resolve eq5116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5116
  have eq5204 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq5137 X0 X1
       grind)
    | exact superpose eq5137 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq5137 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5137 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5137 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq5137 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq5137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5205 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq5137 X0 X1
       grind)
    | exact superpose eq5137 eq11
    | (have j1 := eq5137 X1 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq5137 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5137 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5137 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq5137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5137
  have eq5209 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204
  have eq5216 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5209 X0 X1
       have j1 := eq5205 X0 X1
       grind)
    | (have r₁ := eq5209 (M.op X1 X1) X1
       have r₂ := eq5205 (k X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq5209 X0 X1
       have r₂ := eq5205 X0 X1
       grind)
    | (have r₁ := eq5209 (M.op X1 X1) X1
       have r₂ := eq5205 (M.op X1 X1) X1
       grind)
    | exact resolve eq5209 eq5205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205 eq5209
  have eq5268 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq5216 X1 X0
       grind)
    | exact superpose eq5216 eq9
    | (have j1 := eq5216 X1 X0
       grind)
    | exact resolve eq9 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5323 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5268 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq5268
    | (have j0 := eq5268 X0 X1
       grind)
    | exact resolve eq5268 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5268
  have eq5425 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq5323 (σ X0) X1
       grind)
    | exact superpose eq5323 eq38
    | (have j1 := eq5323 (σ X0) X1
       grind)
    | exact resolve eq38 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5323
  have eq6222 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) X0
       have i₂ := eq5425 X1 (σ X0)
       grind)
    | exact superpose eq5425 eq29
    | (have j1 := eq5425 X1 (σ X0)
       grind)
    | exact resolve eq29 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5425
  have eq6305 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6222 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq6222
    | (have j0 := eq6222 X0 X1
       grind)
    | exact resolve eq6222 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6222
  have eq6343 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6305 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6305
    | (have j0 := eq6305 X0 X1
       grind)
    | exact resolve eq6305 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6305
  have eq6354 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6343 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6343
    | (have j0 := eq6343 X0 X1
       grind)
    | exact resolve eq6343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6343
  have eq6614 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq6354 X1 X0
       grind)
    | exact superpose eq6354 eq10
    | (have j1 := eq6354 X1 X0
       grind)
    | exact resolve eq10 eq6354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6354
  have eq8125 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6614 x y
       grind)
    | exact superpose eq6614 eq16
    | (have j1 := eq6614 x y
       grind)
    | exact resolve eq16 eq6614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq8185 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8125
       have i₂ := eq325 x y
       grind)
    | exact superpose eq325 eq8125
    | (have j1 := eq325 x y
       grind)
    | (have r₁ := eq8125
       have r₂ := eq325 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8125
       have r₂ := eq325 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8125 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq8187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq8125
       have i₂ := eq5216 y x
       grind)
    | exact superpose eq5216 eq8125
    | (have j1 := eq5216 y x
       grind)
    | (have r₁ := eq8125
       have r₂ := eq5216 y x
       grind)
    | (have r₁ := eq8125
       have r₂ := eq5216 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8125
       have r₂ := eq5216 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8125 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216 eq8125
  have eq8188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8187
  have eq8189 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq8188
  have eq8192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8185
  have eq8193 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq8192
  have eq8258 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8189
       grind)
    | exact superpose eq8189 eq16
    | exact resolve eq16 eq8189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8189
  have eq8259 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8258
       have r₂ := eq23 x
       grind)
    | exact resolve eq8258 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8258
  have eq8270 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3671 x y
       have i₂ := eq8259
       grind)
    | exact superpose eq8259 eq3671
    | (have j0 := eq3671 x y
       grind)
    | exact resolve eq3671 eq8259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671 eq8259
  have eq8275 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8270
  have eq8276 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8275
  have eq8370 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8193
       grind)
    | exact superpose eq8193 eq16
    | exact resolve eq16 eq8193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8193
  have eq8371 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8370
       have r₂ := eq23 x
       grind)
    | exact resolve eq8370 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8370
  have eq8465 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8276
       grind)
    | exact superpose eq8276 eq16
    | exact resolve eq16 eq8276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276
  have eq8492 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8465
       have i₂ := eq8371
       grind)
    | exact superpose eq8371 eq8465
    | exact resolve eq8465 eq8371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8371 eq8465
  have eq8497 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq8492
  have eq8498 : (σ x) = (σ y) := by grind
  clear eq8497
  have eq8578 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8498
       grind)
    | exact superpose eq8498 eq16
    | exact resolve eq16 eq8498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8579 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq8498
       grind)
    | exact superpose eq8498 eq9
    | exact resolve eq9 eq8498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8498
  have eq8655 : x = y := by
    first
    | (have i₁ := eq8579
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8579
    | exact resolve eq8579 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8579
  have eq8656 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8578
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq8578
    | exact resolve eq8578 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8578
  have eq8657 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8656
       have i₂ := eq8655
       grind)
    | exact superpose eq8655 eq8656
    | exact resolve eq8656 eq8655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8655 eq8656
  have eq8658 : False := by grind
  exact eq8658
