import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pyy_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq42 : ∀ X0 X1 : G, (σ (k X1 (k x X0))) = (k (σ X1) (k (σ x) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k (k x X0) X1)) = (k (k (σ x) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k x X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq177 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq182 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X0
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X1
       have r₂ := eq177 X0 X1
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X0 X2
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq190 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq182 eq177
    | exact resolve eq177 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : y ≠ y ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq182 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq182
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (k (M.op x y) y) = (M.op (M.op x y) y) := by grind
  clear eq191
  have eq194 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq183 eq177
    | exact resolve eq177 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq190 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq190
       grind)
    | exact resolve eq13 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq199
  have eq202 : y = (k y (M.op x y)) := by
    first
    | exact superpose eq182 eq201
    | exact resolve eq201 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq201
  have eq204 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq194 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq194
       grind)
    | exact resolve eq13 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq204
  have eq207 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq183 eq206
    | exact resolve eq206 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq209 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq202 eq41
    | exact resolve eq41 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq209
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq209
    | exact resolve eq209 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq216 : (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq193 eq190
    | exact resolve eq190 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq222 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq216 eq40
    | exact resolve eq40 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq223 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq222
    | exact resolve eq222 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq279 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq185 X1 X0
       grind)
    | exact superpose eq185 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq185 X0 X1
       grind)
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq281 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq282 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq281
    | exact resolve eq281 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq286 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq282
    | exact resolve eq282 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq348 : (τ (σ y)) = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq207 eq107
    | exact resolve eq107 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq365 : y = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq31 eq348
    | exact resolve eq348 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq384 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq177
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq419 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq434 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq394 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq394 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq394 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq589 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq286 (M.op (M.op X1 X0) (M.op X2 X2)) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq286
    | exact resolve eq286 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq192 eq286
    | exact resolve eq286 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq286
  have eq628 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq599 eq37
    | exact resolve eq37 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq20 eq628
    | (have j0 := eq628 X0
       grind)
    | exact resolve eq628 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq854 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq421 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq421
    | (have j0 := eq421 (σ X0)
       grind)
    | exact resolve eq421 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq1125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq384
       grind)
    | exact superpose eq384 eq39
    | exact resolve eq39 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq384
  have eq1126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1125
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1125
    | exact resolve eq1125 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1126
    | exact resolve eq1126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1361 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 x) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op (M.op X0 x) (M.op X1 X1))
       have i₂ := eq589 x X0 X1
       grind)
    | exact superpose eq589 eq35
    | exact resolve eq35 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1365 : ∀ X0 X1 : G, (τ (σ x)) = (k x (τ (M.op (M.op X0 (σ x)) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (M.op (M.op X1 sF2) (M.op x x))
       have i₂ := eq589 sF2 X1 x
       grind)
    | exact superpose eq589 eq90
    | exact resolve eq90 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq589
  have eq1369 : ∀ X0 X1 : G, x = (k x (τ (M.op (M.op X0 (σ x)) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq29 eq1365
    | exact resolve eq1365 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1373 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 x) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1361 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1361
    | (have j0 := eq1361 X0 X1
       grind)
    | exact resolve eq1361 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq2045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1128 eq386
    | exact resolve eq386 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2054 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2045
       have r₂ := eq27
       grind)
    | exact resolve eq2045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq2065 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2054 eq177
    | exact resolve eq177 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq2075 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2065
    | exact resolve eq2065 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2076 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2075
  have eq2090 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq2076
       grind)
    | exact superpose eq2076 eq177
    | exact resolve eq177 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2093 : (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq189 x y
       have i₂ := eq2076
       grind)
    | exact superpose eq2076 eq189
    | exact resolve eq189 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076
  have eq2099 : (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2093
       have r₂ := eq178
       grind)
    | exact resolve eq2093 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093
  have eq2100 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2090
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2090
    | exact resolve eq2090 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2101 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2100
  have eq2115 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2101 eq207
    | exact resolve eq207 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq2163 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2115 eq1128
    | exact resolve eq1128 eq2115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq2115
  have eq2169 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2163
  have eq2204 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (k y x) (M.op X0 X0)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1373 y X0
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq1373
    | exact resolve eq1373 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2233 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (k y (M.op x y)) (M.op X0 X0)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2101 eq2204
    | exact resolve eq2204 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2246 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op y (M.op X0 X0)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq202 eq2233
    | exact resolve eq2233 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233
  have eq2306 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq2169
       grind)
    | exact superpose eq2169 eq177
    | exact resolve eq177 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2309 : (k y x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq189 x y
       have i₂ := eq2169
       grind)
    | exact superpose eq2169 eq189
    | exact resolve eq189 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq2169
  have eq2315 : (k y x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2309
       have r₂ := eq178
       grind)
    | exact resolve eq2309 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq2309
  have eq2316 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2306
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2306
    | exact resolve eq2306 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq2317 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2316
  have eq2324 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2317 eq28
    | exact resolve eq28 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2360 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2324
    | exact resolve eq2324 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324
  have eq2368 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2360
       grind)
    | exact superpose eq2360 eq18
    | exact resolve eq18 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2374 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq2360
       grind)
    | exact superpose eq2360 eq190
    | exact resolve eq190 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq2360
  have eq2721 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2374 eq187
    | exact resolve eq187 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq2844 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (k y x) (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1373 y X0
       have i₂ := eq2315
       grind)
    | exact superpose eq2315 eq1373
    | exact resolve eq1373 eq2315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373 eq2315
  have eq2875 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (k y (M.op x y)) (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2317 eq2844
    | exact resolve eq2844 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844
  have eq2889 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq202 eq2875
    | exact resolve eq2875 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq2875
  have eq5078 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2246 y
       have i₂ := eq177 y y
       grind)
    | exact superpose eq177 eq2246
    | exact resolve eq2246 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5092 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5078
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5078
    | exact resolve eq5078 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5078
  have eq5266 : ∀ X0 X1 : G, (k (σ X0) (σ x)) = (σ (k X0 (k x (M.op y (M.op X1 X1))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2246 eq42
    | exact resolve eq42 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2246
  have eq5280 : ∀ X0 X1 : G, (k (σ X0) (σ x)) = (σ (k X0 (k (M.op x y) (M.op y (M.op X1 X1))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2101 eq5266
    | exact resolve eq5266 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101 eq5266
  have eq5292 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq599 eq5280
    | exact resolve eq5280 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5280
  have eq5293 : ∀ X0 : G, (k (σ X0) (σ x)) = (k (σ X0) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq5292
    | exact resolve eq5292 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq5292
  have eq5304 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5293 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5293
    | (have j0 := eq5293 y
       grind)
    | exact resolve eq5293 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq5319 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq210 eq5304
    | exact resolve eq5304 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq5304
  have eq5326 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5319 eq386
    | exact resolve eq386 eq5319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq5319
  have eq5340 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5326
  have eq5438 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5340 eq177
    | exact resolve eq177 eq5340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5340
  have eq5455 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5438
    | exact resolve eq5438 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5438
  have eq5456 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5455
  have eq5468 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5456 eq194
    | exact resolve eq194 eq5456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq5506 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq5468 eq187
    | exact resolve eq187 eq5468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq5468
  have eq8476 : ∀ X0 X1 : G, (k (σ x) (σ X1)) = (σ (k (k x (M.op y (M.op X0 X0))) X1)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2889 eq43
    | exact resolve eq43 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq8490 : ∀ X0 X1 : G, (k (σ x) (σ X1)) = (σ (k (k (M.op x y) (M.op y (M.op X0 X0))) X1)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2317 eq8476
    | exact resolve eq8476 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317 eq8476
  have eq8499 : ∀ X1 : G, (k (σ x) (σ X1)) = (σ (k (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq599 eq8490
    | exact resolve eq8490 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq8490
  have eq8505 : ∀ X1 : G, (k (σ x) (σ X1)) = (k (σ (M.op x y)) (σ X1)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq37 eq8499
    | exact resolve eq8499 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq8499
  have eq8917 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq8505 eq630
    | exact resolve eq630 eq8505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq8505
  have eq8938 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2889 eq8917
    | exact resolve eq8917 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2889 eq8917
  have eq8961 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8938 eq28
    | exact resolve eq28 eq8938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8974 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8938 eq223
    | exact resolve eq223 eq8938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq8938
  have eq9016 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq8961
    | exact resolve eq8961 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8961
  have eq9083 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8974 eq420
    | (have j0 := eq420 (σ y) (σ y)
       grind)
    | (have r₁ := eq420 (σ y) (σ y)
       have r₂ := eq8974
       grind)
    | exact resolve eq420 eq8974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq8974
  have eq9084 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9083
  have eq9085 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9084
  have eq9218 : ∀ X0 : G, x = (k x (τ (M.op (M.op X0 (σ x)) (σ y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq9085 eq1369
    | exact resolve eq1369 eq9085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369 eq9085
  have eq14777 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2368 eq2721
    | exact resolve eq2721 eq2368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2368 eq2721
  have eq14904 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14777 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14777
  have eq22571 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq5506
    | (have j0 := eq5506 X0 (σ x)
       grind)
    | exact resolve eq5506 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5506
  have eq22750 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5456 eq22571
    | exact resolve eq22571 eq5456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5456 eq22571
  have eq30031 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5092 eq393
    | (have j0 := eq393 (σ x) (σ x)
       grind)
    | exact resolve eq393 eq5092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5092
  have eq30179 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq30031
    | exact resolve eq30031 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30031
  have eq30180 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30179
  have eq30400 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30180 eq177
    | exact resolve eq177 eq30180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30180
  have eq30462 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq30400
    | exact resolve eq30400 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30400
  have eq30463 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30462
  have eq30490 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30463 eq22750
    | exact resolve eq22750 eq30463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22750 eq30463
  have eq30656 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30490
  have eq30677 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq30656
    | exact resolve eq30656 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30656
  have eq30678 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30677
  have eq30692 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq30678 eq27
    | exact resolve eq27 eq30678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq30695 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq30678 eq183
    | exact resolve eq183 eq30678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq30706 : y = (k y (τ (σ x))) := by
    first
    | exact superpose eq30678 eq365
    | exact resolve eq365 eq30678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq30678
  have eq30719 : y = (k y x) := by
    first
    | exact superpose eq29 eq30706
    | exact resolve eq30706 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq30706
  have eq30723 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9016 eq30692
    | (have r₁ := eq30692
       have r₂ := eq9016
       grind)
    | exact resolve eq30692 eq9016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9016
  have eq30726 : y = (M.op x y) := by grind
  clear eq30723
  have eq30727 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq30726
       grind)
    | exact superpose eq30726 eq18
    | exact resolve eq18 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30728 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq30726
       grind)
    | exact superpose eq30726 eq24
    | exact resolve eq24 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq30737 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq216
       have i₂ := eq30726
       grind)
    | exact superpose eq30726 eq216
    | exact resolve eq216 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq30856 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30728 eq20
    | exact resolve eq20 eq30728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30728
  have eq31086 : x = (k x (τ (M.op (σ y) (σ y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30695 eq9218
    | exact resolve eq9218 eq30695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9218 eq30695
  have eq31156 : x = (k x (τ (M.op (σ y) (σ y)))) := by
    first
    | (have r₁ := eq31086
       have r₂ := eq30692
       grind)
    | exact resolve eq31086 eq30692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31086
  have eq31332 : x ≠ y ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq434 y x
       have i₂ := eq30719
       grind)
    | exact superpose eq30719 eq434
    | (have j0 := eq434 y x
       grind)
    | exact resolve eq434 eq30719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq30719
  have eq31334 : x ≠ y ∨ y = (M.op y x) := by grind
  clear eq31332
  have eq31336 : x ≠ (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq31334
       have i₂ := eq30726
       grind)
    | exact superpose eq30726 eq31334
    | exact resolve eq31334 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31334
  have eq31346 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq31336
       have i₂ := eq30726
       grind)
    | exact superpose eq30726 eq31336
    | exact resolve eq31336 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31336
  have eq31662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30737 eq854
    | (have j0 := eq854 (M.op x y)
       grind)
    | exact resolve eq854 eq30737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq30737
  have eq31678 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq31662
  have eq31679 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq31678
    | exact resolve eq31678 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31678
  have eq31682 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30856 eq31679
    | exact resolve eq31679 eq30856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30856 eq31679
  have eq33443 : x = (M.op x x) ∨ x = (M.op x (τ (M.op (σ y) (σ y)))) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) x) := by
    first
    | exact superpose eq31156 eq393
    | (have j0 := eq393 x x
       grind)
    | exact resolve eq393 eq31156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq31156
  have eq33452 : x = (M.op x (τ (σ y))) ∨ x = (M.op x x) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) x) := by
    first
    | exact superpose eq31682 eq33443
    | exact resolve eq33443 eq31682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33443
  have eq33463 : x = (M.op x y) ∨ x = (M.op x x) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) x) := by
    first
    | exact superpose eq31 eq33452
    | exact resolve eq33452 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33452
  have eq33472 : x = (M.op x y) ∨ x = (M.op x x) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) x) := by
    first
    | (have i₁ := eq33463
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33463
    | exact resolve eq33463 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq33463
  have eq33476 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31682 eq33472
    | exact resolve eq33472 eq31682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31682 eq33472
  have eq33480 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq33476
    | exact resolve eq33476 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33476
  have eq33484 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33480
       have i₂ := eq30726
       grind)
    | exact superpose eq30726 eq33480
    | exact resolve eq33480 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30726 eq33480
  have eq33486 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq33484
       have r₂ := eq31346
       grind)
    | exact resolve eq33484 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31346 eq33484
  have eq39555 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq33486 eq177
    | exact resolve eq177 eq33486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq33486
  have eq39617 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30727 eq39555
    | exact resolve eq39555 eq30727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39555
  have eq39652 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14904 x
       have i₂ := eq39617
       grind)
    | exact superpose eq39617 eq14904
    | exact resolve eq14904 eq39617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14904 eq39617
  have eq39887 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq39652
  have eq39951 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30727 eq39887
    | exact resolve eq39887 eq30727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30727 eq39887
  have eq39952 : x = (M.op x y) := by grind
  clear eq39951
  have eq39974 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq39952
       grind)
    | exact superpose eq39952 eq22
    | exact resolve eq22 eq39952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39952
  have eq40048 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39974 eq20
    | exact resolve eq20 eq39974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq39974
  have eq40122 : False := by grind
  exact eq40122

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_pxx_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
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
  have eq174 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq179 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq179 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x y
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ x) (σ y)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq182 eq179
    | exact resolve eq179 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : y ≠ y ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq182 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq182
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq193 : (M.op x y) = (k (M.op x y) y) := by grind
  clear eq192
  have eq194 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq183 eq179
    | exact resolve eq179 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq183 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq183
       grind)
    | exact resolve eq13 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq197 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq196
  have eq203 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq193 eq40
    | exact resolve eq40 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq193
  have eq204 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq203
    | exact resolve eq203 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq209 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq194 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq194
       grind)
    | exact resolve eq13 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq209
  have eq313 : (τ (σ y)) = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq210 eq107
    | exact resolve eq107 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq210
  have eq330 : y = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq31 eq313
    | exact resolve eq313 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq364 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq422 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq197 eq152
    | exact resolve eq152 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq197
  have eq1068 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq364
       grind)
    | exact superpose eq364 eq39
    | exact resolve eq39 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1068
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1068
    | exact resolve eq1068 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1071 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1069
    | exact resolve eq1069 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1071 eq365
    | exact resolve eq365 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1086 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1079
       have r₂ := eq27
       grind)
    | exact resolve eq1079 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1090 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1086 eq27
    | exact resolve eq27 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1086 eq194
    | exact resolve eq194 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1086 eq422
    | (have r₁ := eq422
       have r₂ := eq1086
       grind)
    | exact resolve eq422 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq1104 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1086
  have eq1105 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1100
  have eq1107 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1105
       have r₂ := eq1104
       grind)
    | exact resolve eq1105 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1105
  have eq1110 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1071 eq1107
    | exact resolve eq1107 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq1107
  have eq1111 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1094 eq1110
    | exact resolve eq1110 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq1110
  have eq1112 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1111
       have r₂ := eq1090
       grind)
    | exact resolve eq1111 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq1111
  have eq1123 : y = (k y (τ (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1112 eq330
    | exact resolve eq330 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq1112
  have eq1130 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1123
    | exact resolve eq1123 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1132 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1130
       have r₂ := eq174
       grind)
    | exact resolve eq1130 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1134 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq364
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq364
    | exact resolve eq364 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq1132
  have eq1137 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1134
  have eq1142 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq18
    | exact resolve eq18 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1143 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq24
    | exact resolve eq24 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq190
    | exact resolve eq190 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1156 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq421
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq421
    | (have r₁ := eq421
       have r₂ := eq1137
       grind)
    | exact resolve eq421 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq1157 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq447
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq447
    | exact resolve eq447 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq1137
  have eq1163 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq1156
  have eq1164 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1163
  have eq1167 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1143
    | exact resolve eq1143 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1231 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1148 eq16
    | exact resolve eq16 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1164 eq1148
    | exact resolve eq1148 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq1164
  have eq1347 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq1324
  have eq1372 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1347 eq39
    | exact resolve eq39 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1373 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1372
    | exact resolve eq1372 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1375 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1167 eq1373
    | exact resolve eq1373 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1384 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1375 eq141
    | exact resolve eq141 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1375
  have eq1389 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1384
    | exact resolve eq1384 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1384
  have eq1392 : y = (k y x) := by
    first
    | (have r₁ := eq1389
       have r₂ := eq174
       grind)
    | exact resolve eq1389 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1389
  have eq1399 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq39
    | exact resolve eq39 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1392
  have eq1402 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1399
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1399
    | exact resolve eq1399 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1399
  have eq1408 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1402 eq365
    | exact resolve eq365 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq1402
  have eq1412 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1408
  have eq1418 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1412 eq27
    | exact resolve eq27 eq1412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1422 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1412 eq194
    | exact resolve eq194 eq1412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1443 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1167 eq1418
    | (have r₁ := eq1418
       have r₂ := eq1167
       grind)
    | exact resolve eq1418 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq1418
  have eq1444 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1443
  have eq1478 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1422 eq16
    | exact resolve eq16 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1509 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1157 eq395
    | (have j0 := eq395 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq395 (M.op x y) (τ (M.op (σ x) (σ y)))
       have r₂ := eq1157
       grind)
    | exact resolve eq395 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1585 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq1509
  have eq1598 : (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1444 eq1585
    | exact resolve eq1585 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq1605 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1598
    | exact resolve eq1598 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1606 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1444 eq1605
    | exact resolve eq1605 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444 eq1605
  have eq1607 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1606
    | exact resolve eq1606 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1606
  have eq5038 : x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1607 eq179
    | exact resolve eq179 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq5062 : x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1142 eq5038
    | exact resolve eq5038 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038
  have eq5063 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq5062
  have eq5084 : x = (M.op x (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5063 eq1231
    | exact resolve eq1231 eq5063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq5063
  have eq5095 : x = (M.op x (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq5084
  have eq5100 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1142 eq5095
    | exact resolve eq5095 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5095
  have eq5104 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1142 eq5100
    | exact resolve eq5100 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq5100
  have eq5105 : x = (M.op x y) := by grind
  clear eq5104
  have eq5107 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5105
       grind)
    | exact superpose eq5105 eq22
    | exact resolve eq22 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5105
  have eq5119 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5107 eq20
    | exact resolve eq20 eq5107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5107
  have eq5160 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq5119 eq204
    | exact resolve eq204 eq5119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq5210 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq5160 eq395
    | (have j0 := eq395 (σ y) (σ x)
       grind)
    | (have r₁ := eq395 (σ y) (σ x)
       have r₂ := eq5160
       grind)
    | exact resolve eq395 eq5160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq5160
  have eq5211 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq5210
  have eq5900 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq5211 eq179
    | exact resolve eq179 eq5211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq5211
  have eq5920 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5900
    | exact resolve eq5900 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5900
  have eq5947 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5920 eq1478
    | exact resolve eq1478 eq5920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq5920
  have eq5957 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5947
  have eq5960 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5957
    | exact resolve eq5957 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5957
  have eq5967 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1412 eq5960
    | exact resolve eq5960 eq1412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412 eq5960
  have eq5971 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5967
    | exact resolve eq5967 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5967
  have eq5972 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5971
  have eq5977 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5972 eq27
    | exact resolve eq27 eq5972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5972
  have eq6005 : False := by grind
  exact eq6005

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_y_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
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
  clear eq23
  have eq80 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2 X0
       have i₂ := eq14 (σ X0) (k X1 (σ X2))
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (σ X0) (k X1 (σ X2))
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
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
  have eq671 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X2) = X2 ∨ (k X0 (σ X2)) = (σ (M.op (τ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq81 X0 X2
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 (τ X0) X1
       have j1 := eq81 X0 X2
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq81 X0 (τ X0)
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq81 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq679 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq678 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq680 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X2) = X2 ∨ (k X0 (σ X2)) = (σ (M.op (τ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq671 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq681 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq679 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq679
    | (have j0 := eq679 X0
       grind)
    | exact resolve eq679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq685 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq681 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq681
    | exact resolve eq681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq702 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq685 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq685
    | (have j0 := eq685 X0
       grind)
    | exact resolve eq685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq706 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq702 X0
       grind)
    | exact superpose eq702 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq702 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq702 X0
       grind)
    | exact resolve eq12 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq716 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq706 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq736 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq716 X0 X1
       grind)
    | exact superpose eq716 eq10
    | (have j1 := eq716 X0 X1
       grind)
    | exact resolve eq10 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq774 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq736
    | (have j0 := eq736 X0 X0
       grind)
    | exact resolve eq736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq816 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq774 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq817 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq915 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq817 (σ X0)
       grind)
    | exact superpose eq817 eq15
    | exact resolve eq15 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq817 (τ X0)
       grind)
    | exact superpose eq817 eq32
    | exact resolve eq32 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq921 X0
       have i₂ := eq817 X0
       grind)
    | exact superpose eq817 eq921
    | exact resolve eq921 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq943 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq915 X0
       have i₂ := eq817 X0
       grind)
    | exact superpose eq817 eq915
    | exact resolve eq915 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq915
  have eq1134 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq943 X0
       grind)
    | exact superpose eq943 eq9
    | exact resolve eq9 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6259 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = X2 ∨ (k (σ X0) (σ X2)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq680 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq680
    | exact resolve eq680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq6339 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6259 X0 X1 X2
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq6259
    | (have j0 := eq6259 X0 X1 X2
       grind)
    | exact resolve eq6259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6259
  have eq17316 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq80 X2 X0 X1
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq80 X2 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (k X1 (σ X2))
       have r₂ := eq80 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq80 X0 X1 X2
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq17317 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17316 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17316
  have eq17318 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17317 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17317
  have eq17319 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k X2 (k (τ X0) X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17318 X0 X1 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq17318
    | (have j0 := eq17318 X0 X1 X2
       grind)
    | exact resolve eq17318 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17318
  have eq17390 : ∀ X0 X1 X2 : G, (σ X2) = (σ (M.op X2 X2)) ∨ (k X0 (σ X1)) = (σ (k X2 (k (τ X0) X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17319 X0 X1 X2
       have i₂ := eq943 X2
       grind)
    | exact superpose eq943 eq17319
    | (have j0 := eq17319 X0 X1 X2
       grind)
    | exact resolve eq17319 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17319
  have eq18149 : ∀ X0 X1 X2 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq6339 X0 X2 X1
       grind)
    | exact superpose eq6339 eq10
    | (have j1 := eq6339 X0 X2 X1
       grind)
    | exact resolve eq10 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq18254 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18149 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq18149
    | (have j0 := eq18149 X0 X1 X1
       grind)
    | exact resolve eq18149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18149
  have eq18538 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq18254 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18254
  have eq18539 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq18538 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18538
  have eq18681 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq18539 (σ X0) X1
       grind)
    | exact superpose eq18539 eq29
    | (have j1 := eq18539 (σ X0) X1
       grind)
    | exact resolve eq29 eq18539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq18690 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq18539 (σ X0) (σ X1)
       grind)
    | exact superpose eq18539 eq15
    | (have j1 := eq18539 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq18539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18911 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 X1) (σ (M.op X0 X0))))) ∨ (σ X0) = (M.op (M.op X1 X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18681 X0 (M.op (M.op X1 X1) (σ (M.op X0 X0)))
       have i₂ := eq1134 X0 X1
       grind)
    | exact superpose eq1134 eq18681
    | exact resolve eq18681 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18681
  have eq19260 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (σ (M.op X0 X0))) ∨ (k X0 (τ (M.op (M.op X1 X1) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18911 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18911
    | (have j0 := eq18911 X0 X1
       grind)
    | exact resolve eq18911 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18911
  have eq21435 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18690 x y
       grind)
    | exact superpose eq18690 eq16
    | (have j1 := eq18690 x y
       grind)
    | exact resolve eq16 eq18690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18690
  have eq275907 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (M.op (M.op X1 X1) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1134 X0 X1
       have i₂ := eq19260 X0 X1
       grind)
    | exact superpose eq19260 eq1134
    | (have j1 := eq19260 X0 X1
       grind)
    | exact resolve eq1134 eq19260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq19260
  have eq275981 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (M.op (M.op X1 X1) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq275907 X0 X1
       have i₂ := eq943 X0
       grind)
    | exact superpose eq943 eq275907
    | (have j0 := eq275907 X0 X1
       grind)
    | exact resolve eq275907 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq275907
  have eq276118 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (τ X0) = (k (τ X0) (τ (M.op (M.op X1 X1) (σ (τ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq275981 (τ X0) X1
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq275981
    | exact resolve eq275981 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275981
  have eq276655 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (τ X0) = (k (τ X0) (τ (M.op (M.op X1 X1) (σ (τ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq276118 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq276118
    | (have j0 := eq276118 X0 X1
       grind)
    | exact resolve eq276118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276118
  have eq276680 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (k (τ X0) (τ (M.op (M.op X1 X1) (σ (τ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq276655 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq276655
    | (have j0 := eq276655 X0 X1
       grind)
    | exact resolve eq276655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276655
  have eq276693 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (M.op (M.op X1 X1) (σ (τ (M.op X0 X0)))))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq276680 X0 X1
       have i₂ := eq32 (M.op (M.op X1 X1) (σ (τ (M.op X0 X0)))) X0
       grind)
    | exact superpose eq32 eq276680
    | (have j0 := eq276680 X0 X1
       grind)
    | exact resolve eq276680 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq276680
  have eq276704 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (τ (k X0 (M.op (M.op X1 X1) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq276693 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq276693
    | (have j0 := eq276693 X0 X1
       grind)
    | exact resolve eq276693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276693
  have eq278764 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (τ (k X0 (M.op (M.op X2 X2) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq276704 X0 X2
       grind)
    | exact superpose eq276704 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq276704 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq276704 X0 X1
       grind)
    | exact resolve eq12 eq276704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276704
  have eq279128 : ∀ X0 X1 X2 : G, (τ X0) = (τ (k X0 (M.op (M.op X2 X2) (M.op X0 X0)))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq278764 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278764
  have eq286075 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (M.op (M.op X1 X1) (M.op X0 X0)))
       have i₂ := eq279128 X0 X2 X1
       grind)
    | exact superpose eq279128 eq11
    | (have j1 := eq279128 X0 X2 X2
       grind)
    | exact resolve eq11 eq279128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279128
  have eq286722 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq286075 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq286075
    | (have j0 := eq286075 X0 X1 X2
       grind)
    | exact resolve eq286075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286075
  have eq289034 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq286722 X0 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286722
  have eq289037 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq289034 X0 X1
       grind)
    | (have r₁ := eq289034 X0 X1
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq289034 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289034
  have eq289301 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq289037 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq289037
    | exact resolve eq289037 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289037
  have eq290022 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 X1) (M.op (τ X0) (τ X0)))
       have i₂ := eq289301 (τ X0) X1
       grind)
    | exact superpose eq289301 eq17
    | exact resolve eq17 eq289301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289301
  have eq290384 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq290022 X0 X1
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq290022
    | exact resolve eq290022 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290022
  have eq290620 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq290384 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290384
    | exact resolve eq290384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290384
  have eq297166 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 X1) (τ (M.op (τ X0) (τ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op X1 X1) (τ (M.op (τ X0) (τ X0)))))
       have i₂ := eq290620 (τ X0) X1
       grind)
    | exact superpose eq290620 eq17
    | exact resolve eq17 eq290620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290620
  have eq297568 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 X1) (τ (τ (M.op X0 X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq297166 X0 X1
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq297166
    | exact resolve eq297166 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297166
  have eq297881 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op X1 X1) (τ (τ (M.op X0 X0))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq297568 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq297568
    | exact resolve eq297568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297568
  have eq331314 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (M.op (τ X0) (τ X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op (M.op X1 X1) (τ (τ (M.op (τ X0) (τ X0)))))))
       have i₂ := eq297881 (τ X0) X1
       grind)
    | exact superpose eq297881 eq17
    | exact resolve eq17 eq297881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297881
  have eq331726 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq331314 X0 X1
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq331314
    | exact resolve eq331314 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331314
  have eq332050 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq331726 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq331726
    | exact resolve eq331726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331726
  have eq402175 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op (τ X0) (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (M.op (τ X0) (τ X0)))))))))
       have i₂ := eq332050 (τ X0) X1
       grind)
    | exact superpose eq332050 eq17
    | exact resolve eq17 eq332050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332050
  have eq402613 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (M.op X0 X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq402175 X0 X1
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq402175
    | exact resolve eq402175 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402175
  have eq402950 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (M.op X0 X0))))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq402613 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq402613
    | exact resolve eq402613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402613
  have eq557175 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (M.op (τ X0) (τ X0))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (M.op (τ X0) (τ X0)))))))))))
       have i₂ := eq402950 (τ X0) X1
       grind)
    | exact superpose eq402950 eq17
    | exact resolve eq17 eq402950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402950
  have eq557711 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq557175 X0 X1
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq557175
    | exact resolve eq557175 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557175
  have eq558097 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq557711 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq557711
    | exact resolve eq557711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557711
  have eq857987 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (M.op (τ X0) (τ X0))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (M.op (τ X0) (τ X0)))))))))))))
       have i₂ := eq558097 (τ X0) X1
       grind)
    | exact superpose eq558097 eq17
    | exact resolve eq17 eq558097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558097
  have eq858603 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq857987 X0 X1
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq857987
    | exact resolve eq857987 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857987
  have eq859029 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq858603 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq858603
    | exact resolve eq858603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858603
  have eq1404131 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (k X1 (σ X2)) = (σ (k (τ X0) (k (τ X1) X2))) ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17390 X1 X2 (τ X0)
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq17390
    | (have j0 := eq17390 X1 X2 (τ X0)
       grind)
    | exact resolve eq17390 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq17390
  have eq1405194 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (k X1 (σ X2)) = (σ (k (τ X0) (k (τ X1) X2))) ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1404131 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1404131
    | (have j0 := eq1404131 X0 X1 X2
       grind)
    | exact resolve eq1404131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404131
  have eq1405219 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X2)) = (σ (k (τ X0) (k (τ X1) X2))) ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1405194 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1405194
    | (have j0 := eq1405194 X0 X1 X2
       grind)
    | exact resolve eq1405194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405194
  have eq1405234 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (k X0 (σ (k (τ X1) X2))) ∨ (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1405219 X0 X1 X2
       have i₂ := eq17 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq17 eq1405219
    | (have j0 := eq1405219 X0 X1 X2
       grind)
    | exact resolve eq1405219 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405219
  have eq1405249 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (k X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1405234 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq1405234
    | (have j0 := eq1405234 X0 X1 X2
       grind)
    | exact resolve eq1405234 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405234
  have eq1405263 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (k X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1405249 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1405249
    | (have j0 := eq1405249 X0 X1 X2
       grind)
    | exact resolve eq1405249 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405249
  have eq1405273 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (k X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1405263 X0 X1 X2
       have i₂ := eq17 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq17 eq1405263
    | (have j0 := eq1405263 X0 X1 X2
       grind)
    | exact resolve eq1405263 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405263
  have eq1405282 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (k X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1405273 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq1405273
    | (have j0 := eq1405273 X0 X1 X2
       grind)
    | exact resolve eq1405273 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1405273
  have eq1405289 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (k X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1405282 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq1405282 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1405282 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405282
  have eq1449547 : ∀ X0 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (k X2 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1405289 X0 X0 (σ (σ (σ (σ (σ (M.op (M.op x x) (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))))))))
       have i₂ := eq859029 X0 x
       grind)
    | exact superpose eq859029 eq1405289
    | exact resolve eq1405289 eq859029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1450503 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) ≠ (M.op X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1405289 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405289
  have eq1450546 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1450503 X0 X1 X2
       have j1 := eq18539 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq1450503 X0 X1 X2
       have r₂ := eq18539 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq1450503 eq18539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18539 eq1450503
  have eq1453233 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1449547 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449547
  have eq1456861 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1450546 X0 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))))))))
       have i₂ := eq859029 X0 X1
       grind)
    | exact superpose eq859029 eq1450546
    | exact resolve eq1450546 eq859029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859029 eq1450546
  have eq1471249 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21435
       have i₂ := eq1456861 y x
       grind)
    | exact superpose eq1456861 eq21435
    | exact resolve eq21435 eq1456861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21435
  have eq1471252 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1471249
  have eq1482661 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1471252
       grind)
    | exact superpose eq1471252 eq16
    | exact resolve eq16 eq1471252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1482663 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1453233 (σ x) (σ y)
       have i₂ := eq1471252
       grind)
    | exact superpose eq1471252 eq1453233
    | (have j0 := eq1453233 (σ x) (σ y)
       grind)
    | (have r₁ := eq1453233 (σ x) (σ y)
       have r₂ := eq1471252
       grind)
    | exact resolve eq1453233 eq1471252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453233 eq1471252
  have eq1482664 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq1482663
  have eq1482666 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1482664
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1482664
    | exact resolve eq1482664 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482664
  have eq1482670 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1482666
       have i₂ := eq1456861 y x
       grind)
    | exact superpose eq1456861 eq1482666
    | exact resolve eq1482666 eq1456861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456861 eq1482666
  have eq1482672 : False := by grind
  exact eq1482672

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_x_pyx_x_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq270 (τ X0)
       grind)
    | exact superpose eq270 eq31
    | exact resolve eq31 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq287
    | exact resolve eq287 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq9
    | exact resolve eq9 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq371 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X1 X1)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq346 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq346
    | exact resolve eq346 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq478 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq371 X0 X0
       have i₂ := eq300 (M.op X0 X0)
       grind)
    | exact superpose eq300 eq371
    | exact resolve eq371 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq371
  have eq650 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq348 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq348
    | exact resolve eq348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X2 (k X0 (σ X1))) ∨ (k (k X0 (σ X1)) X2) = (M.op X2 (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq348 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq348
    | exact resolve eq348 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq656 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq348 X1 (σ X0)
       grind)
    | exact superpose eq348 eq15
    | (have j1 := eq348 X1 (σ X0)
       grind)
    | exact resolve eq15 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq689 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq650 X1 (σ X0)
       grind)
    | exact superpose eq650 eq22
    | (have j1 := eq650 X1 (σ X0)
       grind)
    | exact resolve eq22 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq650
  have eq776 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) X0) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq689 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq478 X0
       grind)
    | exact superpose eq478 eq689
    | exact resolve eq689 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq689
  have eq838 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq776 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq776
    | (have j0 := eq776 X0
       grind)
    | exact resolve eq776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq861 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq838 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq838
    | (have j0 := eq838 X0
       grind)
    | exact resolve eq838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq1791 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq656 x y
       grind)
    | exact superpose eq656 eq16
    | (have j1 := eq656 x y
       grind)
    | exact resolve eq16 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1862 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq656 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq1987 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1862 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1862
    | (have j0 := eq1862 (τ X1) (τ X0)
       grind)
    | exact resolve eq1862 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1996 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1987 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1987
    | (have j0 := eq1987 X0 X1
       grind)
    | exact resolve eq1987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987
  have eq1999 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1996 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1996
    | (have j0 := eq1996 X0 X1
       grind)
    | exact resolve eq1996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq2000 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1999 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1999
    | (have j0 := eq1999 X0 X1
       grind)
    | exact resolve eq1999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2001 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2000 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2000
    | (have j0 := eq2000 X0 X1
       grind)
    | exact resolve eq2000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq24213 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) X0) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))
       have i₂ := eq861 (τ X0)
       grind)
    | exact superpose eq861 eq18
    | (have j1 := eq861 (τ X0)
       grind)
    | exact resolve eq18 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq861
  have eq24279 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) X0) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq24213 X0
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq24213
    | (have j0 := eq24213 X0
       grind)
    | exact resolve eq24213 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24213
  have eq24338 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) X0) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq24279 X0
       have i₂ := eq294 (M.op X0 X0)
       grind)
    | exact superpose eq294 eq24279
    | (have j0 := eq24279 X0
       grind)
    | exact resolve eq24279 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24279
  have eq24389 : ∀ X0 : G, (σ (τ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq24338 X0
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq24338
    | (have j0 := eq24338 X0
       grind)
    | exact resolve eq24338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24338
  have eq24439 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq24389 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24389
    | (have j0 := eq24389 X0
       grind)
    | exact resolve eq24389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24389
  have eq24488 : ∀ X0 : G, (σ (τ X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24439 X0
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq24439
    | (have j0 := eq24439 X0
       grind)
    | exact resolve eq24439 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24439
  have eq24537 : ∀ X0 : G, (σ (τ X0)) = (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24488 X0
       have i₂ := eq294 (M.op X0 X0)
       grind)
    | exact superpose eq294 eq24488
    | (have j0 := eq24488 X0
       grind)
    | exact resolve eq24488 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq24488
  have eq24574 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24537 X0
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq24537
    | (have j0 := eq24537 X0
       grind)
    | exact resolve eq24537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24537
  have eq24600 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24574 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24574
    | (have j0 := eq24574 X0
       grind)
    | exact resolve eq24574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24574
  have eq82422 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) X2) ∨ (k (k X0 (σ X1)) X2) = (M.op X2 (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) X2
       have i₂ := eq651 X0 X1 X2
       grind)
    | exact superpose eq651 eq13
    | (have j0 := eq13 (k X0 (σ X1)) X2
       have j1 := eq651 X0 X1 (k X0 (σ X1))
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) X2
       have r₂ := eq651 X0 X1 X2
       grind)
    | exact resolve eq13 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq82435 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) X2) ∨ (k (k X0 (σ X1)) X2) = (M.op X2 (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq82422 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82422
  have eq82442 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) X2) = (M.op X2 (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq82435 X0 X1 X2
       have j1 := eq12 (k X0 (σ X1)) X2
       grind)
    | (have r₁ := eq82435 X0 X1 X2
       have r₂ := eq12 (k X0 (σ X1)) X1
       grind)
    | exact resolve eq82435 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82435
  have eq82878 : ∀ X0 X1 X2 : G, (k (k X1 X0) X2) = (M.op X2 (k X1 X0)) ∨ (k X1 X0) = (k (k X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82442 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82442
    | exact resolve eq82442 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82442
  have eq83370 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82878 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       have i₂ := eq24600 X0
       grind)
    | exact superpose eq24600 eq82878
    | (have j1 := eq24600 X0
       grind)
    | exact resolve eq82878 eq24600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24600 eq82878
  have eq84437 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq83370 X0 X1
       grind)
    | exact superpose eq83370 eq9
    | (have j1 := eq83370 X0 X1
       grind)
    | exact resolve eq9 eq83370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83370
  have eq84752 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq84437 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq84437 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq84437 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84437
  have eq85200 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1791
       have i₂ := eq84752 y x
       grind)
    | exact superpose eq84752 eq1791
    | (have j1 := eq84752 y x
       grind)
    | exact resolve eq1791 eq84752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791
  have eq85201 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq84752 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84752
  have eq85202 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by grind
  clear eq85200
  have eq85425 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq85201 (σ y) (σ x)
       have i₂ := eq85202
       grind)
    | exact superpose eq85202 eq85201
    | (have j0 := eq85201 (σ y) (σ x)
       grind)
    | (have r₁ := eq85201 (σ y) (σ x)
       have r₂ := eq85202
       grind)
    | exact resolve eq85201 eq85202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85202
  have eq85426 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq85425
  have eq85429 : y = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq85426
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq85426
    | exact resolve eq85426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85426
  have eq85732 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1862 x y
       have i₂ := eq85429
       grind)
    | exact superpose eq85429 eq1862
    | (have j0 := eq1862 x y
       grind)
    | (have r₁ := eq1862 x y
       have r₂ := eq85429
       grind)
    | exact resolve eq1862 eq85429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85429
  have eq85823 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq85732
  have eq85826 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1862 x y
       grind)
    | (have r₁ := eq85823
       have r₂ := eq1862 x y
       grind)
    | exact resolve eq85823 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862 eq85823
  have eq85830 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85826
       grind)
    | exact superpose eq85826 eq16
    | exact resolve eq16 eq85826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85833 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq85201 (σ y) (σ x)
       have i₂ := eq85826
       grind)
    | exact superpose eq85826 eq85201
    | (have j0 := eq85201 (σ y) (σ x)
       grind)
    | (have r₁ := eq85201 (σ y) (σ x)
       have r₂ := eq85826
       grind)
    | exact resolve eq85201 eq85826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85201 eq85826
  have eq85834 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq85833
  have eq85837 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq85834
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq85834
    | exact resolve eq85834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85834
  have eq85869 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq85837
       grind)
    | exact superpose eq85837 eq10
    | exact resolve eq10 eq85837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85837
  have eq86035 : y = (k y x) := by
    first
    | (have i₁ := eq85869
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq85869
    | exact resolve eq85869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85869
  have eq86057 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2001 y x
       have i₂ := eq86035
       grind)
    | exact superpose eq86035 eq2001
    | (have j0 := eq2001 y x
       grind)
    | (have r₁ := eq2001 y x
       have r₂ := eq86035
       grind)
    | exact resolve eq2001 eq86035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001 eq86035
  have eq86144 : y = (M.op x y) := by grind
  clear eq86057
  have eq86149 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq85830
       have i₂ := eq86144
       grind)
    | exact superpose eq86144 eq85830
    | exact resolve eq85830 eq86144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85830 eq86144
  have eq86160 : False := by grind
  exact eq86160

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq38
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
  have eq74 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq40
    | exact resolve eq40 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq99 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq143 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X1 X1)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq78
    | exact resolve eq78 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq172 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq89
    | exact resolve eq89 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq201 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq177
    | (have j0 := eq177 X0 X1 X2
       grind)
    | exact resolve eq177 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq177
  have eq204 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq172 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq172
    | (have j0 := eq172 X0 X1
       grind)
    | exact resolve eq172 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq172
  have eq210 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq204 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq204 (σ X0) (M.op X0 X0)
       have r₂ := eq76 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq204 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq204
  have eq474 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq210
    | exact resolve eq210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq510 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq474 X1 (σ X0)
       grind)
    | exact superpose eq474 eq29
    | (have j1 := eq474 X1 (σ X0)
       grind)
    | exact resolve eq29 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq799 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq143 X0 X0
       have i₂ := eq40 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq143
    | exact resolve eq143 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq143
  have eq1262 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (M.op X0 X0) (M.op X0 X0))))) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq510 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq799 X0
       grind)
    | exact superpose eq799 eq510
    | exact resolve eq510 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq799
  have eq1322 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1262 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq1262
    | (have j0 := eq1262 X0
       grind)
    | exact resolve eq1262 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1346 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1322 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1322
    | (have j0 := eq1322 X0
       grind)
    | exact resolve eq1322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1888 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq201 X0 X1 X2
       grind)
    | exact superpose eq201 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq201 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq201 X0 X1 X2
       grind)
    | exact resolve eq13 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq1890 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1888 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1891 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1890 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq1893 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k X2 (k (τ X0) X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1891 X0 X1 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq1891
    | (have j0 := eq1891 X0 X1 X2
       grind)
    | exact resolve eq1891 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1891
  have eq42900 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1346 (τ X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq1346
    | exact resolve eq1346 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq43113 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq42900 X0
       have i₂ := eq99 (M.op X0 X0)
       grind)
    | exact superpose eq99 eq42900
    | (have j0 := eq42900 X0
       grind)
    | exact resolve eq42900 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq42900
  have eq43180 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq43113 X0
       have i₂ := eq44 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       grind)
    | exact superpose eq44 eq43113
    | (have j0 := eq43113 X0
       grind)
    | exact resolve eq43113 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43113
  have eq43245 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (τ X0) = (τ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq43180 X0
       have i₂ := eq42 (M.op X0 X0)
       grind)
    | exact superpose eq42 eq43180
    | (have j0 := eq43180 X0
       grind)
    | exact resolve eq43180 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq43180
  have eq43308 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (τ X0) = (τ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq43245 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43245
    | (have j0 := eq43245 X0
       grind)
    | exact resolve eq43245 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43245
  have eq55479 : ∀ X0 X1 X2 : G, (k X0 (σ (τ X1))) = (σ (k X2 (τ (k X0 X1)))) ∨ (M.op (k X0 (σ (τ X1))) (σ X2)) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) ∨ (M.op (σ X2) (k X0 (σ (τ X1)))) = (σ (k X2 (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1893 X1 (τ X0) X2
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq1893
    | (have j0 := eq1893 X0 (τ X1) X2
       grind)
    | exact resolve eq1893 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1893
  have eq55855 : ∀ X0 X1 X2 : G, (k X0 (σ (τ X1))) = (k (σ X2) (k X0 X1)) ∨ (M.op (k X0 (σ (τ X1))) (σ X2)) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) ∨ (M.op (σ X2) (k X0 (σ (τ X1)))) = (σ (k X2 (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55479 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq55479
    | (have j0 := eq55479 X0 X1 X2
       grind)
    | exact resolve eq55479 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55479
  have eq55906 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (σ X2) (k X0 X1)) ∨ (M.op (k X0 (σ (τ X1))) (σ X2)) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) ∨ (M.op (σ X2) (k X0 (σ (τ X1)))) = (σ (k X2 (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55855 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq55855
    | (have j0 := eq55855 X0 X1 X2
       grind)
    | exact resolve eq55855 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55855
  have eq55954 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (σ X2)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = (k (σ X2) (k X0 X1)) ∨ (M.op (σ X2) (k X0 (σ (τ X1)))) = (σ (k X2 (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55906 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55906
    | (have j0 := eq55906 X0 X1 X2
       grind)
    | exact resolve eq55906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55906
  have eq55997 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X0 (σ (τ X1)))) = (k (σ X2) (k X0 X1)) ∨ (M.op (k X0 X1) (σ X2)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = (k (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55954 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq55954
    | (have j0 := eq55954 X0 X1 X2
       grind)
    | exact resolve eq55954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq55954
  have eq56028 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X0 X1)) = (k (σ X2) (k X0 X1)) ∨ (M.op (k X0 X1) (σ X2)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = (k (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55997 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq55997
    | (have j0 := eq55997 X0 X1 X2
       grind)
    | exact resolve eq55997 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55997
  have eq56049 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (σ X2) (k X0 X1)) ∨ (M.op (σ X2) (k X0 X1)) = (k (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq56028 X0 X1 X2
       have j1 := eq12 (σ X2) (k X0 X1)
       grind)
    | (have r₁ := eq56028 X0 X1 X2
       have r₂ := eq12 (σ X2) (k X0 X1)
       grind)
    | exact resolve eq56028 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56028
  have eq59322 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq43308 X0
       grind)
    | exact superpose eq43308 eq9
    | (have j1 := eq43308 X0
       grind)
    | exact resolve eq9 eq43308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43308
  have eq59867 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq59322 X0
       grind)
    | exact superpose eq59322 eq11
    | (have j1 := eq59322 X0
       grind)
    | exact resolve eq11 eq59322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59322
  have eq60095 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59867 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59867
    | (have j0 := eq59867 X0
       grind)
    | exact resolve eq59867 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59867
  have eq150374 : ∀ X0 X1 X2 : G, (k X1 X2) ≠ (M.op (σ X0) (k X1 X2)) ∨ (k (σ X0) (k X1 X2)) = (M.op (σ X0) (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq56049 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56049
  have eq150390 : ∀ X0 X1 X2 : G, (k (σ X0) (k X1 X2)) = (M.op (σ X0) (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq150374 X0 X1 X2
       have j1 := eq474 (k X1 X2) (σ X0)
       grind)
    | (have r₁ := eq150374 X0 X1 X2
       have r₂ := eq474 (k X1 X2) (σ X0)
       grind)
    | exact resolve eq150374 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq150374
  have eq151034 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq150390 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq150390
    | exact resolve eq150390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150390
  have eq151500 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq151034 X0 X0 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq151034
    | exact resolve eq151034 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq151507 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq151034 X0 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq60095 X0
       grind)
    | exact superpose eq60095 eq151034
    | (have j1 := eq60095 X0
       grind)
    | exact resolve eq151034 eq60095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60095 eq151034
  have eq153584 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151500 X0 X1
       have i₂ := eq151507 X0 X1
       grind)
    | exact superpose eq151507 eq151500
    | (have j1 := eq151507 X0 X1
       grind)
    | exact resolve eq151500 eq151507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151500 eq151507
  have eq209351 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq153584 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153584
  have eq209352 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq209351 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209351
  have eq216365 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq209352 (σ X0) (σ X1)
       grind)
    | exact superpose eq209352 eq15
    | exact resolve eq15 eq209352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216719 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq216365 X0 X1
       have i₂ := eq209352 X0 X1
       grind)
    | exact superpose eq209352 eq216365
    | exact resolve eq216365 eq209352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209352 eq216365
  have eq247741 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq216719 x y
       grind)
    | exact superpose eq216719 eq16
    | (have r₁ := eq16
       have r₂ := eq216719 x y
       grind)
    | exact resolve eq16 eq216719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216719
  have eq248070 : False := by grind
  exact eq248070

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_x_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  clear eq17
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
  clear eq22
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
  have eq68 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq31
    | exact resolve eq31 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq68
    | exact resolve eq68 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
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
  have eq91 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq91 X0 (σ X1)
       grind)
    | exact superpose eq91 eq15
    | (have j1 := eq91 X0 (σ X1)
       grind)
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1006 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq18
    | (have j1 := eq101 X0 X1
       grind)
    | exact resolve eq18 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1146 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1149 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq1166 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1149 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq1149
    | (have j0 := eq1149 X0 X1
       grind)
    | exact resolve eq1149 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1167 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq1146
    | (have j0 := eq1146 X0 X1
       grind)
    | exact resolve eq1146 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1146
  have eq1180 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1166 X0 X1
       have j1 := eq976 X0 X1
       grind)
    | (have r₁ := eq1166 X0 X1
       have r₂ := eq976 X0 X1
       grind)
    | (have r₁ := eq1166 X0 (M.op X0 X0)
       have r₂ := eq976 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1166 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq1166
  have eq1181 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1167 X0 X1
       have j1 := eq1006 X0 X1
       grind)
    | (have r₁ := eq1167 X0 X1
       have r₂ := eq1006 X0 X1
       grind)
    | (have r₁ := eq1167 X0 (τ (M.op X0 X0))
       have r₂ := eq1006 X0 (τ (M.op X0 X0))
       grind)
    | exact resolve eq1167 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq1167
  have eq1191 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1181 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1181
    | exact resolve eq1181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1341 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1191 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1191
    | (have j0 := eq1191 X0 X1
       grind)
    | exact resolve eq1191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq2020 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1180 x y
       grind)
    | exact superpose eq1180 eq16
    | (have j1 := eq1180 x y
       grind)
    | exact resolve eq16 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2103 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq2238 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2103 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2103
    | (have j0 := eq2103 (τ X1) (τ X0)
       grind)
    | exact resolve eq2103 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2246 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2238 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2238
    | (have j0 := eq2238 X0 X1
       grind)
    | exact resolve eq2238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2250 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2246 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2246
    | (have j0 := eq2246 X0 X1
       grind)
    | exact resolve eq2246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246
  have eq2251 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2250 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2250
    | (have j0 := eq2250 X0 X1
       grind)
    | exact resolve eq2250 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250
  have eq2252 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2251 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2251
    | (have j0 := eq2251 X0 X1
       grind)
    | exact resolve eq2251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2353 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2020
       have i₂ := eq1341 x y
       grind)
    | exact superpose eq1341 eq2020
    | (have j1 := eq1341 (σ x) (σ y)
       grind)
    | (have r₁ := eq2020
       have r₂ := eq1341 x y
       grind)
    | exact resolve eq2020 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341 eq2020
  have eq2354 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2353
  have eq2357 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2354
       grind)
    | exact superpose eq2354 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2354
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2354
       grind)
    | exact resolve eq13 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2358 : y ≠ (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2354
       grind)
    | exact superpose eq2354 eq12
    | exact resolve eq12 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq2359 : y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2357
  have eq2360 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq2359
       have r₂ := eq2358
       grind)
    | exact resolve eq2359 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358 eq2359
  have eq2363 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2360
       grind)
    | exact superpose eq2360 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2360
       grind)
    | exact resolve eq13 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2364 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2360
       grind)
    | exact superpose eq2360 eq12
    | exact resolve eq12 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2365 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq2363
  have eq2366 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2364
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq2364
    | exact resolve eq2364 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2364
  have eq2367 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2365
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq2365
    | exact resolve eq2365 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2369 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2366
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2366
    | exact resolve eq2366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2370 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2367
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2367
    | exact resolve eq2367 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367
  have eq2371 : y = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq2370
       have r₂ := eq2369
       grind)
    | exact resolve eq2370 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369 eq2370
  have eq2381 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq2103 x y
       have i₂ := eq2371
       grind)
    | exact superpose eq2371 eq2103
    | (have j0 := eq2103 x y
       grind)
    | (have r₁ := eq2103 x y
       have r₂ := eq2371
       grind)
    | exact resolve eq2103 eq2371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2386 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq2381
  have eq2391 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq2103 x y
       grind)
    | (have r₁ := eq2386
       have r₂ := eq2103 x y
       grind)
    | exact resolve eq2386 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103 eq2386
  have eq2394 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2391
       grind)
    | exact superpose eq2391 eq16
    | exact resolve eq16 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2395 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2391
       grind)
    | exact superpose eq2391 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2391
       grind)
    | exact resolve eq13 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2396 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2391
       grind)
    | exact superpose eq2391 eq12
    | exact resolve eq12 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2397 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq2395
  have eq2398 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2396
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq2396
    | exact resolve eq2396 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq2399 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2397
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq2397
    | exact resolve eq2397 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2397
  have eq2401 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2398
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2398
    | exact resolve eq2398 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq2402 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2399
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2399
    | exact resolve eq2399 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq2403 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq2402
       have r₂ := eq2401
       grind)
    | exact resolve eq2402 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401 eq2402
  have eq2412 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq2403
       grind)
    | exact superpose eq2403 eq10
    | exact resolve eq10 eq2403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq2468 : y = (k y x) := by
    first
    | (have i₁ := eq2412
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2412
    | exact resolve eq2412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412
  have eq2477 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2252 y x
       have i₂ := eq2468
       grind)
    | exact superpose eq2468 eq2252
    | (have j0 := eq2252 y x
       grind)
    | (have r₁ := eq2252 y x
       have r₂ := eq2468
       grind)
    | exact resolve eq2252 eq2468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252 eq2468
  have eq2480 : y = (M.op x y) := by grind
  clear eq2477
  have eq2486 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2394
       have i₂ := eq2480
       grind)
    | exact superpose eq2480 eq2394
    | exact resolve eq2394 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394 eq2480
  have eq2492 : False := by grind
  exact eq2492

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq194 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq199 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq191 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq191 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq200 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq194 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq194 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq194 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq209 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq212 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X1
       have j1 := eq210 X0 X1
       grind)
    | (have r₁ := eq212 X0 X1
       have r₂ := eq210 X0 X1
       grind)
    | exact resolve eq212 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq212
  have eq218 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq217
    | exact resolve eq217 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq217 x y
       grind)
    | exact superpose eq217 eq16
    | exact resolve eq16 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq324 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq218 X0 (τ X1)
       grind)
    | exact superpose eq218 eq18
    | exact resolve eq18 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq218
  have eq341 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq324
    | exact resolve eq324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq349 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq341
    | exact resolve eq341 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq370 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq229
       have i₂ := eq349 x y
       grind)
    | exact superpose eq349 eq229
    | exact resolve eq229 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq349
  have eq371 : False := by grind
  exact eq371

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
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
  have eq270 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq272 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq275 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq273 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq273 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq295 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq278 (τ X0)
       grind)
    | exact superpose eq278 eq31
    | exact resolve eq31 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq295 X0
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq295
    | exact resolve eq295 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq381 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq275 X1 X0
       grind)
    | exact superpose eq275 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275 (σ y) (σ x)
       grind)
    | exact superpose eq275 eq16
    | (have j1 := eq275 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq389 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq384
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq384
    | exact resolve eq384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq390 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
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
  have eq403 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq390 X0 (σ X1)
       grind)
    | exact superpose eq390 eq22
    | (have j1 := eq390 X0 (σ X1)
       grind)
    | exact resolve eq22 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq421
    | (have j0 := eq421 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq421 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq421 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq457 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 X1) (M.op (τ X0) (τ X0)))
       have i₂ := eq435 (τ X0) X1
       grind)
    | exact superpose eq435 eq17
    | exact resolve eq17 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq462 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq457
    | exact resolve eq457 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq468 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq462
    | exact resolve eq462 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq2387 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq403 (σ X0) X1
       grind)
    | exact superpose eq403 eq28
    | (have j1 := eq403 (σ X0) X1
       grind)
    | exact resolve eq28 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq403
  have eq2398 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2387 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2387
    | (have j0 := eq2387 X0 X1
       grind)
    | exact resolve eq2387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq2415 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2398 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2398
    | (have j0 := eq2398 X0 X1
       grind)
    | exact resolve eq2398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq2426 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2415 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2415
    | (have j0 := eq2415 X0 X1
       grind)
    | exact resolve eq2415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2482 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2426 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2426
    | (have j0 := eq2426 X1 (τ X0)
       grind)
    | exact resolve eq2426 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2519 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq2426 X0 X1
       grind)
    | exact superpose eq2426 eq11
    | (have j1 := eq2426 X0 X1
       grind)
    | exact resolve eq11 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2578 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2519 X0 X1
       have i₂ := eq390 X0 X1
       grind)
    | exact superpose eq390 eq2519
    | (have j0 := eq2519 X0 X1
       have j1 := eq390 X0 X1
       grind)
    | exact resolve eq2519 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2583 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2519 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2519
    | exact resolve eq2519 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq2629 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2583 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2583
    | (have j0 := eq2583 X0 X1
       grind)
    | exact resolve eq2583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583
  have eq2630 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2578 X0 X1
       have j1 := eq421 X0 X1
       grind)
    | (have r₁ := eq2578 X0 X1
       have r₂ := eq421 X0 X1
       grind)
    | exact resolve eq2578 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq2578
  have eq2635 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2629 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2629
    | (have j0 := eq2629 X0 X1
       grind)
    | exact resolve eq2629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629
  have eq2638 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2635 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2635
    | (have j0 := eq2635 X0 X1
       grind)
    | exact resolve eq2635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq2664 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X2)) = (τ (k (k X0 X1) X2)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (k X0 X1)
       have i₂ := eq2638 X0 X1
       grind)
    | exact superpose eq2638 eq31
    | (have j1 := eq2638 X0 X1
       grind)
    | exact resolve eq31 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2665 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op (k X0 X1) (k X0 X1))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq302 (k X0 X1)
       have i₂ := eq2638 X0 X1
       grind)
    | exact superpose eq2638 eq302
    | (have j1 := eq2638 X0 X1
       grind)
    | exact resolve eq302 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2673 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op (k X0 X1) (k X0 X1))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2665 X0 X1
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq2665
    | (have j0 := eq2665 X0 X1
       grind)
    | exact resolve eq2665 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq2674 : ∀ X0 X1 X2 : G, (τ (k X0 X2)) = (τ (k (k X0 X1) X2)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2664 X0 X1 X2
       have i₂ := eq31 X2 X0
       grind)
    | exact superpose eq31 eq2664
    | (have j0 := eq2664 X0 X1 X2
       grind)
    | exact resolve eq2664 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq2724 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (σ (M.op (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq2630 (τ X0) X1
       grind)
    | exact superpose eq2630 eq17
    | (have j1 := eq2630 (τ X0) X1
       grind)
    | exact resolve eq17 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq2733 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2724 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2724
    | (have j0 := eq2724 X0 X1
       grind)
    | exact resolve eq2724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724
  have eq2742 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2733 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2733
    | (have j0 := eq2733 X0 X1
       grind)
    | exact resolve eq2733 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733
  have eq3452 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2482 X0 (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2482
    | exact resolve eq2482 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2482
  have eq3478 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3452 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3452
    | (have j0 := eq3452 X0 X1
       grind)
    | exact resolve eq3452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3452
  have eq3701 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3478 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3478
  have eq4665 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2742 (σ X0) X1
       grind)
    | exact superpose eq2742 eq15
    | (have j1 := eq2742 (σ X0) X1
       grind)
    | exact resolve eq15 eq2742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq4686 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4665 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4665
    | (have j0 := eq4665 X0 X1
       grind)
    | exact resolve eq4665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4665
  have eq15925 : ∀ X0 X1 X2 : G, (τ (k X0 (σ X1))) = (k (τ (k X0 X2)) X1) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (k X0 X2) X1
       have i₂ := eq2674 X0 X2 (σ X1)
       grind)
    | exact superpose eq2674 eq22
    | (have j1 := eq2674 X0 X2 X2
       grind)
    | exact resolve eq22 eq2674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15930 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (k X0 X2) X1) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (k X0 X2) X1)
       have i₂ := eq2674 X0 X2 X1
       grind)
    | exact superpose eq2674 eq11
    | (have j1 := eq2674 X0 X2 X2
       grind)
    | exact resolve eq11 eq2674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq15986 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = (k (k X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15930 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq15930
    | (have j0 := eq15930 X0 X1 X2
       grind)
    | exact resolve eq15930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15930
  have eq15989 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k (τ X0) X1) = (k (τ (k X0 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15925 X0 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq15925
    | (have j0 := eq15925 X0 X1 X2
       grind)
    | exact resolve eq15925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15925
  have eq16055 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k (k X0 X1) X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4686 X0 X1
       have i₂ := eq15986 X0 X2 X1
       grind)
    | exact superpose eq15986 eq4686
    | (have j0 := eq4686 X0 X1
       have j1 := eq15986 X0 X2 X1
       grind)
    | exact resolve eq4686 eq15986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15986
  have eq22571 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X0)) X2) = (k (τ (k (σ X0) (σ X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq15989 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq15989 eq15
    | (have j1 := eq15989 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq15989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15989
  have eq22639 : ∀ X0 X1 X2 : G, (k (k (τ (σ X0)) X1) X2) = (k (τ (σ X0)) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22571 X0 X1 X2
       have i₂ := eq22 (σ X0) X1
       grind)
    | exact superpose eq22 eq22571
    | (have j0 := eq22571 X0 X1 X2
       grind)
    | exact resolve eq22571 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22571
  have eq22703 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (k X0 X1) X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22639 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22639
    | (have j0 := eq22639 X0 X1 X2
       grind)
    | exact resolve eq22639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22639
  have eq61388 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k (k x y) X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq22703 x y X0
       grind)
    | exact superpose eq22703 eq16
    | (have j1 := eq22703 x y X0
       grind)
    | exact resolve eq16 eq22703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22703
  have eq62380 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k (k x y) X0) = (k x X0) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61388 X0
       have i₂ := eq4686 x y
       grind)
    | exact superpose eq4686 eq61388
    | (have j0 := eq61388 X0
       have j1 := eq4686 x y
       grind)
    | exact resolve eq61388 eq4686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4686 eq61388
  have eq62404 : ∀ X0 : G, (k (k x y) X0) = (k x X0) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq62380 X0
       have j1 := eq16055 x y X0
       grind)
    | (have r₁ := eq62380 X0
       have r₂ := eq16055 x y x
       grind)
    | exact resolve eq62380 eq16055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16055 eq62380
  have eq62405 : ∀ X0 : G, (k (k x y) X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq62404 X0
       grind)
    | (have r₁ := eq62404 X0
       have r₂ := eq16
       grind)
    | exact resolve eq62404 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62404
  have eq62547 : (M.op (k x y) (k x y)) = (k x (k x y)) := by
    first
    | (have i₁ := eq278 (k x y)
       have i₂ := eq62405 (k x y)
       grind)
    | exact superpose eq62405 eq278
    | exact resolve eq278 eq62405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq62549 : ∀ X0 : G, (k x X0) = (M.op (k x y) X0) ∨ (k x y) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq390 (k x y) X0
       have i₂ := eq62405 X0
       grind)
    | exact superpose eq62405 eq390
    | exact resolve eq390 eq62405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64949 : ∀ X0 : G, (k X0 (σ (M.op (k x (k x y)) (τ (M.op X0 X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq468 X0 (k x y)
       have i₂ := eq62547
       grind)
    | exact superpose eq62547 eq468
    | exact resolve eq468 eq62547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq70009 : (k x y) = (k x (σ (M.op (k x (k x y)) (τ (M.op (k x y) (k x y)))))) := by
    first
    | (have i₁ := eq62405 (σ (M.op (k x (k x y)) (τ (M.op (k x y) (k x y)))))
       have i₂ := eq64949 (k x y)
       grind)
    | exact superpose eq64949 eq62405
    | exact resolve eq62405 eq64949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62405
  have eq70017 : (k x y) = (k x (σ (M.op (k x (k x y)) (τ (k x (k x y)))))) := by
    first
    | (have i₁ := eq70009
       have i₂ := eq62547
       grind)
    | exact superpose eq62547 eq70009
    | exact resolve eq70009 eq62547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70009
  have eq74972 : ∀ X0 : G, x = (k x y) ∨ (M.op x y) = (k x X0) ∨ (k x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq62549 X0
       have i₂ := eq390 x y
       grind)
    | exact superpose eq390 eq62549
    | (have j1 := eq390 x y
       grind)
    | exact resolve eq62549 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq62549
  have eq323505 : (M.op x y) = (k x y) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq2673 x y
       have i₂ := eq62547
       grind)
    | exact superpose eq62547 eq2673
    | (have j0 := eq2673 x y
       grind)
    | exact resolve eq2673 eq62547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq324509 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq2630 x y
       have i₂ := eq323505
       grind)
    | exact superpose eq323505 eq2630
    | (have j0 := eq2630 x y
       grind)
    | exact resolve eq2630 eq323505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630 eq323505
  have eq324544 : x = (M.op x y) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have r₁ := eq324509
       have r₂ := eq16
       grind)
    | exact resolve eq324509 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324509
  have eq324566 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x y)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq3701 x y
       have i₂ := eq324544
       grind)
    | exact superpose eq324544 eq3701
    | (have j0 := eq3701 x y
       grind)
    | exact resolve eq3701 eq324544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701 eq324544
  have eq324573 : (τ x) = (τ (k x y)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by grind
  clear eq324566
  have eq327467 : (τ (M.op (k x y) (k x y))) = (M.op (τ x) (τ x)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq302 (k x y)
       have i₂ := eq324573
       grind)
    | exact superpose eq324573 eq302
    | exact resolve eq302 eq324573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324573
  have eq327791 : (τ (M.op (k x y) (k x y))) = (τ (M.op x x)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq327467
       have i₂ := eq302 x
       grind)
    | exact superpose eq302 eq327467
    | exact resolve eq327467 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq327467
  have eq327909 : (τ (k x (k x y))) = (τ (M.op x x)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq327791
       have i₂ := eq62547
       grind)
    | exact superpose eq62547 eq327791
    | exact resolve eq327791 eq62547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62547 eq327791
  have eq327910 : (τ (k x (k x y))) = (τ (M.op x x)) := by grind
  clear eq327909
  have eq328050 : (k x y) = (k x (σ (M.op (k x (k x y)) (τ (M.op x x))))) := by
    first
    | (have i₁ := eq70017
       have i₂ := eq327910
       grind)
    | exact superpose eq327910 eq70017
    | exact resolve eq70017 eq327910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70017 eq327910
  have eq328422 : x = (k x y) := by
    first
    | (have i₁ := eq328050
       have i₂ := eq64949 x
       grind)
    | exact superpose eq64949 eq328050
    | exact resolve eq328050 eq64949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64949 eq328050
  have eq2327610 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (k x y) = (M.op (M.op x y) y) := by
    first
    | (have j0 := eq74972 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74972
  have eq2327615 : (M.op x y) = (k x y) ∨ (k x y) = (M.op (M.op x y) y) := by
    first
    | (have j1 := eq275 y x
       grind)
    | (have r₁ := eq2327610
       have r₂ := eq275 y x
       grind)
    | exact resolve eq2327610 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327610
  have eq2327878 : x = (M.op x y) ∨ (k x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2327615
       have i₂ := eq328422
       grind)
    | exact superpose eq328422 eq2327615
    | exact resolve eq2327615 eq328422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327615
  have eq2327880 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2327878
       have i₂ := eq328422
       grind)
    | exact superpose eq328422 eq2327878
    | exact resolve eq2327878 eq328422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327878
  have eq2327881 : x = (M.op x y) ∨ x = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2327880
       have i₂ := eq275 y (M.op x y)
       grind)
    | exact superpose eq275 eq2327880
    | (have j1 := eq275 y x
       grind)
    | exact resolve eq2327880 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327880
  have eq2327898 : x = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by grind
  clear eq2327881
  have eq2328443 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq389
       have i₂ := eq2327898
       grind)
    | exact superpose eq2327898 eq389
    | exact resolve eq389 eq2327898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327898
  have eq2328499 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by grind
  clear eq2328443
  have eq2328502 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2328499
       have i₂ := eq328422
       grind)
    | exact superpose eq328422 eq2328499
    | exact resolve eq2328499 eq328422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328499
  have eq2328545 : (σ (M.op x y)) ≠ (σ x) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2328502
       grind)
    | exact superpose eq2328502 eq16
    | exact resolve eq16 eq2328502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328502
  have eq2328982 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2328545
       have i₂ := eq275 y x
       grind)
    | exact superpose eq275 eq2328545
    | (have j1 := eq275 y x
       grind)
    | exact resolve eq2328545 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq2328545
  have eq2328987 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by grind
  clear eq2328982
  have eq2328988 : (M.op x y) = (k x y) := by grind
  clear eq2328987
  have eq2328995 : x = (M.op x y) := by
    first
    | (have i₁ := eq2328988
       have i₂ := eq328422
       grind)
    | exact superpose eq328422 eq2328988
    | exact resolve eq2328988 eq328422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328988
  have eq2328999 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq389
       have i₂ := eq2328995
       grind)
    | exact superpose eq2328995 eq389
    | exact resolve eq389 eq2328995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq2329057 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq2328999
  have eq2329061 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2329057
       have i₂ := eq328422
       grind)
    | exact superpose eq328422 eq2329057
    | exact resolve eq2329057 eq328422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328422 eq2329057
  have eq2329101 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2329061
       grind)
    | exact superpose eq2329061 eq16
    | exact resolve eq16 eq2329061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329061
  have eq2329445 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2329101
       have i₂ := eq2328995
       grind)
    | exact superpose eq2328995 eq2329101
    | exact resolve eq2329101 eq2328995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328995 eq2329101
  have eq2329446 : False := by grind
  exact eq2329446
