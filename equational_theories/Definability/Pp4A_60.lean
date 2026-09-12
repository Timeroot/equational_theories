import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4538`: `x ◇ (y ◇ z) = (y ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation4538 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4538 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4538.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X3) := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op x X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X1) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq177 X2 x
       have i₂ := eq177 X0 x
       grind)
    | (have i₁ := eq177 X0 (M.op x y)
       have i₂ := eq177 (M.op x (M.op x y)) x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq215 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op x y) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq191 eq16
    | exact resolve eq16 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq195 eq174
    | exact resolve eq174 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq260 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq246 eq191
    | exact resolve eq191 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (σ x) X2) X3)) = (M.op (M.op X0 (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X0 X2 (M.op (σ x) (σ y))
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq178 eq246
    | exact resolve eq246 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq246
  have eq309 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op (σ x) X2) X3)) = (M.op (k (M.op x y) (M.op x y)) X2) := by
    intro X1 X2 X3
    first
    | exact superpose eq296 eq293
    | exact resolve eq293 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq325 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op (k (M.op x y) (M.op x y)) X2) := by
    intro X2
    first
    | (have i₁ := eq309 x X2 X2
       have i₂ := eq215 x (M.op sF2 X2) X2
       grind)
    | exact superpose eq215 eq309
    | exact resolve eq309 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq329 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X2) := by
    intro X2
    first
    | exact superpose eq260 eq325
    | exact resolve eq325 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq970 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X1 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq215
    | exact resolve eq215 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1052 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq260 eq970
    | exact resolve eq970 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1086 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ y = (k x y) := by
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
  have eq1089 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1089
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1089
    | exact resolve eq1089 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1094 : (M.op x y) ≠ (k x x) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq1086
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1086
    | exact resolve eq1086 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1163 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq1166 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1249 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1166
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1166
    | exact resolve eq1166 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1250 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1163
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1163
    | exact resolve eq1163 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1794 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1052
    | exact resolve eq1052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1804 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq174 (k X0 X0)
       have i₂ := eq1052 X0 (k X0 X0)
       grind)
    | exact superpose eq1052 eq174
    | exact resolve eq174 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq2186 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (k (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq174 (σ (k X0 X0))
       have i₂ := eq1794 X0 (σ (k X0 X0))
       grind)
    | exact superpose eq1794 eq174
    | exact resolve eq174 eq1794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2220 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (σ (k (k X0 X0) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2186 X0
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq2186
    | exact resolve eq2186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2232 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2220 x
       have i₂ := eq1804 x
       grind)
    | exact superpose eq1804 eq2220
    | exact resolve eq2220 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq2220
  have eq2235 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq2232
    | exact resolve eq2232 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq2237 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2235
    | exact resolve eq2235 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235
  have eq2239 : (k (M.op x y) (M.op x y)) = (τ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2237 eq133
    | exact resolve eq133 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq5970 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1250
       grind)
    | exact superpose eq1250 eq40
    | exact resolve eq40 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq5971 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq5970
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5970
    | exact resolve eq5970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970
  have eq5973 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq5971
    | exact resolve eq5971 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5971
  have eq8046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq5973 eq1249
    | exact resolve eq1249 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8053 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq8046
       have r₂ := eq27
       grind)
    | exact resolve eq8046 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8046
  have eq10399 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq8053 eq1091
    | (have r₁ := eq1091
       have r₂ := eq8053
       grind)
    | exact resolve eq1091 eq8053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq8053
  have eq10418 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq10399
  have eq10419 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq10418
  have eq10427 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq10419 eq5973
    | exact resolve eq5973 eq10419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5973
  have eq10430 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq10419 eq90
    | exact resolve eq90 eq10419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq10419
  have eq10433 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10427
  have eq10437 : y = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq10430
    | exact resolve eq10430 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10430
  have eq10440 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10437
       have r₂ := eq1094
       grind)
    | exact resolve eq10437 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq10437
  have eq10444 : y = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1250
       have i₂ := eq10440
       grind)
    | exact superpose eq10440 eq1250
    | exact resolve eq1250 eq10440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq10445 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq10440
       grind)
    | exact superpose eq10440 eq35
    | exact resolve eq35 eq10440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq10440
  have eq10447 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10444
  have eq10450 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10445
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10445
    | exact resolve eq10445 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10445
  have eq10455 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10450 eq1249
    | exact resolve eq1249 eq10450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249 eq10450
  have eq10459 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10455
  have eq10497 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq10433
       grind)
    | exact superpose eq10433 eq39
    | exact resolve eq39 eq10433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10433
  have eq10518 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10497
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10497
    | exact resolve eq10497 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10497
  have eq10524 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq10518
    | exact resolve eq10518 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10518
  have eq10532 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq39
    | exact resolve eq39 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10539 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1794 x X0
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq1794
    | exact resolve eq1794 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794 eq10447
  have eq10550 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq10539
    | (have j0 := eq10539 X0
       grind)
    | exact resolve eq10539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10539
  have eq10553 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10532
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10532
    | exact resolve eq10532 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10532
  have eq10559 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq10553
    | exact resolve eq10553 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10553
  have eq10606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10459 eq10524
    | exact resolve eq10524 eq10459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10524
  have eq10623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10606
  have eq10631 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq10623
       have r₂ := eq27
       grind)
    | exact resolve eq10623 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10623
  have eq10635 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq10631 eq296
    | exact resolve eq296 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq10649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10559 eq10459
    | exact resolve eq10459 eq10559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10459 eq10559
  have eq10666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq10649
  have eq10679 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10666
       have r₂ := eq27
       grind)
    | exact resolve eq10666 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10666
  have eq10686 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq10679 eq27
    | exact resolve eq27 eq10679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10679
  have eq11392 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10635 eq26
    | (have j1 := eq10635 (σ x)
       grind)
    | exact resolve eq26 eq10635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11398 : (σ y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10631 eq11392
    | exact resolve eq11392 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10631 eq11392
  have eq11454 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq11398 eq329
    | exact resolve eq329 eq11398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq11458 : (σ y) = (τ (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11398 eq2239
    | exact resolve eq2239 eq11398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239 eq11398
  have eq11493 : (σ x) = (σ y) ∨ x = y ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31 eq11458
    | exact resolve eq11458 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11458
  have eq11500 : y = (τ (σ x)) ∨ x = y ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11493 eq31
    | exact resolve eq31 eq11493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11493
  have eq11527 : x = y ∨ x = y ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq11500
    | exact resolve eq11500 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11500
  have eq11528 : (σ (M.op x y)) = (σ y) ∨ y = (σ y) ∨ x = y := by grind
  clear eq11527
  have eq11530 : (M.op x y) = (τ (σ y)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq11528 eq28
    | exact resolve eq28 eq11528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11528
  have eq11561 : y = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq11530
    | exact resolve eq11530 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11530
  have eq11564 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11561
       grind)
    | exact superpose eq11561 eq18
    | exact resolve eq18 eq11561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11576 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11561
  have eq11863 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11564 eq10635
    | exact resolve eq10635 eq11564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10635 eq11564
  have eq11891 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq11863
  have eq11904 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11891
       have r₂ := eq10686
       grind)
    | exact resolve eq11891 eq10686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11891
  have eq12497 : (σ y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11454 eq10550
    | exact resolve eq10550 eq11454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10550 eq11454
  have eq12503 : (σ y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12497
  have eq12507 : (σ y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12503
       have r₂ := eq10686
       grind)
    | exact resolve eq12503 eq10686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10686 eq12503
  have eq12563 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11904 eq12507
    | exact resolve eq12507 eq11904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11904 eq12507
  have eq12590 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12563
       have r₂ := eq11576
       grind)
    | exact resolve eq12563 eq11576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11576 eq12563
  have eq12602 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq12590 eq31
    | exact resolve eq31 eq12590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12590
  have eq12646 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq12602
    | exact resolve eq12602 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12602
  have eq12647 : y = (M.op x y) ∨ x = y := by grind
  clear eq12646
  have eq12659 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq12647
       grind)
    | exact superpose eq12647 eq18
    | exact resolve eq18 eq12647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12660 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq12647
       grind)
    | exact superpose eq12647 eq24
    | exact resolve eq24 eq12647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12647
  have eq12677 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq12660
    | exact resolve eq12660 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12660
  have eq12678 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq191 eq12659
    | exact resolve eq12659 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12659
  have eq12679 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq260 eq12678
    | exact resolve eq12678 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12678
  have eq12734 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq12679 eq41
    | exact resolve eq41 eq12679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq12760 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq12734
    | exact resolve eq12734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12734
  have eq12772 : (σ (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2237 eq12760
    | exact resolve eq12760 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237 eq12760
  have eq12778 : (σ y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12677 eq12772
    | exact resolve eq12772 eq12677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12772
  have eq12781 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12679 eq12778
    | exact resolve eq12778 eq12679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12778
  have eq12787 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12781 eq26
    | exact resolve eq26 eq12781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12852 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq191 eq12787
    | exact resolve eq12787 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq12787
  have eq12860 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq260 eq12852
    | exact resolve eq12852 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq12852
  have eq12863 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq12679 eq12860
    | exact resolve eq12860 eq12679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12679 eq12860
  have eq12868 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12863 eq27
    | exact resolve eq27 eq12863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12863
  have eq12881 : (M.op x y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12677 eq12868
    | exact resolve eq12868 eq12677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12677 eq12868
  have eq12884 : (M.op x y) ≠ (σ y) ∨ x = y := by grind
  clear eq12881
  have eq12886 : x = y := by
    first
    | (have r₁ := eq12884
       have r₂ := eq12781
       grind)
    | exact resolve eq12884 eq12781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12781 eq12884
  have eq12890 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12886
       grind)
    | exact superpose eq12886 eq18
    | exact resolve eq18 eq12886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12891 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq12886
       grind)
    | exact superpose eq12886 eq24
    | exact resolve eq24 eq12886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12886
  have eq12907 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12891
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12891
    | exact resolve eq12891 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12891
  have eq12908 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq12890
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq12890
    | exact resolve eq12890 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12890
  have eq12911 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12907 eq26
    | exact resolve eq26 eq12907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12907
  have eq12947 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12911
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq12911
    | exact resolve eq12911 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq12911
  have eq12956 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq12908
       grind)
    | exact superpose eq12908 eq39
    | exact resolve eq39 eq12908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq12908
  have eq12977 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12956
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12956
    | exact resolve eq12956 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12956
  have eq12982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12947 eq12977
    | exact resolve eq12977 eq12947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12947 eq12977
  have eq12984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12982
    | exact resolve eq12982 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12982
  have eq12986 : False := by grind
  exact eq12986

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pxy_Equation455 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law455 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq9 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq38 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq43 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq43
  have eq61 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq26
    | exact resolve eq26 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq30
    | (have j0 := eq30 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq711 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq85 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq85 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq85 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq725 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq711
  have eq904 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq725
       grind)
    | exact superpose eq725 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq725
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq725
       grind)
    | exact resolve eq13 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq906 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq904
  have eq907 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq906
  have eq909 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq907
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq907
    | exact resolve eq907 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq964 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (τ X0) X1
       have i₂ := eq143 X0
       grind)
    | exact superpose eq143 eq26
    | exact resolve eq26 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq1980 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq10
    | exact resolve eq10 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq2009 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1980
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1980
    | exact resolve eq1980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2010 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq2009
       have r₂ := eq13 x y
       grind)
    | exact resolve eq2009 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq4138 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30 x y
       have i₂ := eq2010
       grind)
    | exact superpose eq2010 eq30
    | (have j0 := eq30 x y
       grind)
    | exact resolve eq30 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq4139 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq2010
       grind)
    | exact superpose eq2010 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq4140 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq4139
  have eq4141 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4138
  have eq140442 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq4141
       grind)
    | exact superpose eq4141 eq16
    | exact resolve eq16 eq4141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4141
  have eq148467 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq140442
       have i₂ := eq4140
       grind)
    | exact superpose eq4140 eq140442
    | exact resolve eq140442 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140 eq140442
  have eq148470 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq148467
  have eq148471 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq148470
  have eq158016 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq148471
       grind)
    | exact superpose eq148471 eq9
    | exact resolve eq9 eq148471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148471
  have eq158116 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq158016 X0
       have i₂ := eq26 (σ x) (σ y)
       grind)
    | exact superpose eq26 eq158016
    | exact resolve eq158016 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158016
  have eq168674 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq964 (σ y) X0
       have i₂ := eq158116 (σ y)
       grind)
    | exact superpose eq158116 eq964
    | exact resolve eq964 eq158116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq158116
  have eq169126 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq168674 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq168674
    | exact resolve eq168674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168674
  have eq182827 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq169126 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169126
  have eq182828 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq182827
  have eq196401 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq182828
       grind)
    | exact superpose eq182828 eq9
    | exact resolve eq9 eq182828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182828
  have eq196454 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq196401 X0
       have i₂ := eq26 x y
       grind)
    | exact superpose eq26 eq196401
    | exact resolve eq196401 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq196401
  have eq222002 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq196454 X0
       grind)
    | exact superpose eq196454 eq10
    | (have j1 := eq196454 X0
       grind)
    | exact resolve eq10 eq196454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196454
  have eq222593 : ∀ X0 : G, x = y ∨ (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq222002 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq222002
    | (have j0 := eq222002 X0
       grind)
    | exact resolve eq222002 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222002
  have eq222594 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq222593 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222593
  have eq251863 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 y X0
       have i₂ := eq222594 y
       grind)
    | exact superpose eq222594 eq61
    | exact resolve eq61 eq222594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq278246 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq251863 (σ x)
       grind)
    | exact superpose eq251863 eq16
    | exact resolve eq16 eq251863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251863
  have eq351549 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq278246
       have i₂ := eq222594 x
       grind)
    | exact superpose eq222594 eq278246
    | exact resolve eq278246 eq222594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222594 eq278246
  have eq351556 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq351549
  have eq351557 : x = y := by grind
  clear eq351556
  have eq367233 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq351557
       grind)
    | exact superpose eq351557 eq16
    | exact resolve eq16 eq351557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351557
  have eq367234 : False := by grind
  exact eq367234

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pxy_pxx_pyx_Equation4554 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq52 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X2 x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 x x X0 X4
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X3 X0) ∨ (M.op (M.op X0 X1) X0) = (k X2 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X2 X3) X2)
       have r₂ := eq14 X0 (M.op X2 X3) X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ X2 ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X2 X3) X2
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X2 X3) X2)
       have r₂ := eq14 X0 (M.op X2 X3) X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq96 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq96
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) X0) (M.op X2 X0)) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) ∨ (M.op X2 X0) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) := by
    intro X0 X1 X2
    grind
  have eq111 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    grind
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq97
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq116
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq158 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq141
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq141
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq141 eq10
    | exact resolve eq10 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq141 eq16
    | exact resolve eq16 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq158
  have eq179 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq41
    | exact resolve eq41 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq221 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq224 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 X2 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 X0 X3
       have i₂ := eq14 X0 X1 sF3 X3
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq261 eq54
    | exact resolve eq54 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq59 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : (M.op (M.op x y) x) = (k (M.op x x) x) ∨ x = (M.op (M.op x x) x) := by grind
  have eq304 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 (M.op x x)
       have i₂ := eq59 X2 x
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    intro X1
    first
    | (have i₁ := eq53 X1 (M.op x x)
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq53
    | exact resolve eq53 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq309 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op X1 x)
       have i₂ := eq59 sF3 X1
       grind)
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq60 X0 x
       have i₂ := eq14 X0 x sF2 x
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by grind
  have eq328 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X1
    first
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq397 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq55 X0 (M.op x x) X2
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq261 eq55
    | exact resolve eq55 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq261
  have eq844 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X4 X0 X2 (M.op x x)
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq52
    | exact resolve eq52 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 X3))) ≠ X3 ∨ (M.op X0 (M.op X1 (M.op X2 X3))) = (k (M.op X3 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 (M.op X2 x) X2
       have i₂ := eq52 X0 X1 X2 X3 x
       grind)
    | exact superpose eq52 eq13
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1997 : ∀ X2 : G, x ≠ (M.op (M.op x y) x) ∨ (M.op (M.op x y) x) = (k (M.op x X2) x) := by
    intro X2
    first
    | (have i₁ := eq73 x x x x
       have i₂ := eq59 x x
       grind)
    | exact superpose eq59 eq73
    | exact resolve eq73 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2000 : ∀ X2 : G, (σ x) ≠ (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) X2) (σ x)) := by
    intro X2
    first
    | exact superpose eq60 eq73
    | exact resolve eq73 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2330 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) X1) (τ X0))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq111 (τ X0) X1
       grind)
    | exact superpose eq111 eq39
    | (have j1 := eq111 (τ X0) X1
       grind)
    | exact resolve eq39 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq2458 : ∀ X0 X2 X3 : G, (M.op X2 X0) ≠ (M.op (M.op (M.op x y) x) X0) ∨ (M.op (M.op (M.op x y) x) X0) = (k X3 (M.op X2 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq72 X0 (M.op x x) X2 X3
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq72
    | exact resolve eq72 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2533 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) ≠ (M.op X2 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (k X3 (M.op X2 (M.op x y))) := by
    intro X0 X2 X3
    first
    | exact superpose eq224 eq72
    | (have r₁ := eq72 (M.op x y) x X2 X2
       have r₂ := eq224 (M.op (M.op x y) x) X2
       grind)
    | (have r₁ := eq72 (M.op x y) x X2 X0
       have r₂ := eq224 X0 (M.op (M.op x y) x)
       grind)
    | exact resolve eq72 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2538 : ∀ X1 X2 : G, (M.op X1 (M.op x y)) ≠ (M.op (M.op (M.op x y) x) y) ∨ (M.op (M.op (M.op x y) x) y) = (k X2 (M.op X1 (M.op x y))) := by
    intro X1 X2
    first
    | exact superpose eq308 eq72
    | exact resolve eq72 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq2648 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) x) y) = (k X2 (M.op X1 (M.op x y))) := by
    intro X1 X2
    first
    | (have j0 := eq2538 X1 X2
       grind)
    | (have r₁ := eq2538 X1 X2
       have r₂ := eq308 X1
       grind)
    | exact resolve eq2538 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq2538
  have eq2653 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) = (k X3 (M.op X2 (M.op x y))) := by
    intro X0 X2 X3
    first
    | (have j0 := eq2533 X0 X2 X3
       grind)
    | (have r₁ := eq2533 X0 X2 X3
       have r₂ := eq224 X0 X2
       grind)
    | (have r₁ := eq2533 X2 X0 X3
       have r₂ := eq224 X0 X2
       grind)
    | exact resolve eq2533 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533
  have eq3415 : ∀ X0 X2 : G, (k (M.op (M.op (M.op x y) x) X0) (M.op X2 X0)) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op (M.op x y) x) X0)) ∨ (M.op X2 X0) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq109 X0 (M.op x x) X2
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq109
    | exact resolve eq109 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq4521 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 (M.op x y)))) = (σ (M.op X0 (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2653 eq35
    | exact resolve eq35 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2653
  have eq5851 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op (M.op x y) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq262 eq492
    | exact resolve eq492 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq38979 : x = (M.op (M.op x y) x) ∨ (M.op (M.op x y) x) = (k (M.op x x) x) := by
    first
    | (have i₁ := eq299
       have i₂ := eq298 x
       grind)
    | exact superpose eq298 eq299
    | exact resolve eq299 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq299
  have eq38980 : (M.op (M.op x y) x) = (k (M.op x x) x) := by
    first
    | (have j1 := eq1997 x
       grind)
    | (have r₁ := eq38979
       have r₂ := eq1997 x
       grind)
    | exact resolve eq38979 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997 eq38979
  have eq39076 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq317 eq318
    | exact resolve eq318 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq318
  have eq39077 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have j1 := eq2000 (σ x)
       grind)
    | (have r₁ := eq39076
       have r₂ := eq2000 x
       grind)
    | exact resolve eq39076 eq2000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000 eq39076
  have eq60976 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq179
    | (have j0 := eq179 x
       grind)
    | exact resolve eq179 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq61046 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq60976
  have eq61079 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61046
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq61046
    | exact resolve eq61046 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61046
  have eq61094 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq61079
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq61079 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61079
  have eq61103 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq61094 eq50
    | exact resolve eq50 eq61094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq61173 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq201 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq201
    | (have j0 := eq201 y
       grind)
    | exact resolve eq201 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq61243 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq61173
  have eq61271 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq61243
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq61243
    | exact resolve eq61243 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61243
  have eq61282 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq61271
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq61271 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61271
  have eq61292 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq61282 eq121
    | exact resolve eq121 eq61282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq61357 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq221
    | (have j0 := eq221 (M.op x y)
       grind)
    | exact resolve eq221 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq61424 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq61357
  have eq61451 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141 eq61424
    | exact resolve eq61424 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61424
  have eq61464 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq61451
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq61451 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61451
  have eq61476 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq61464 eq164
    | exact resolve eq164 eq61464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq62683 : ∀ X0 X1 : G, (σ (M.op X0 (M.op x y))) = (σ (k y (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq4521 eq37
    | exact resolve eq37 eq4521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq62757 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) := by
    intro X0
    first
    | exact superpose eq2648 eq62683
    | exact resolve eq62683 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62683
  have eq64498 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op x y) x) X3) ≠ X3 ∨ (M.op X0 (M.op X1 (M.op X2 X3))) = (k (M.op X3 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq951 X0 X1 X2 X3 X4
       have i₂ := eq844 X3 X0 X1 X2
       grind)
    | exact superpose eq844 eq951
    | (have j0 := eq951 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq951 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq64499 : ∀ X3 X4 : G, (M.op (M.op (M.op x y) x) X3) ≠ X3 ∨ (k (M.op X3 X4) X3) = (M.op (M.op (M.op x y) x) X3) := by
    intro X3 X4
    first
    | (have i₁ := eq64498 x x x X3 X4
       have i₂ := eq844 X3 x x x
       grind)
    | exact superpose eq844 eq64498
    | (have j0 := eq64498 x x x X3 X4
       grind)
    | exact resolve eq64498 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq64498
  have eq74454 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (M.op x y) x) (τ X0))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2330 X0 x
       have i₂ := eq492 (τ X0) x
       grind)
    | exact superpose eq492 eq2330
    | (have j0 := eq2330 X0 x
       grind)
    | exact resolve eq2330 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330
  have eq74455 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (M.op x y) x) (τ X0))) ∨ (τ X0) = (M.op (M.op (M.op x y) x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq74454 X0
       have i₂ := eq492 (τ X0) (τ X0)
       grind)
    | exact superpose eq492 eq74454
    | (have j0 := eq74454 X0
       grind)
    | exact resolve eq74454 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq74454
  have eq74549 : ∀ X0 : G, (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) = (τ (σ (M.op (M.op (M.op x y) x) (τ (σ X0))))) ∨ (τ (σ X0)) = (M.op (M.op (M.op x y) x) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq397 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq74455 (σ X0)
       grind)
    | exact superpose eq74455 eq397
    | (have j1 := eq74455 (σ X0)
       grind)
    | exact resolve eq397 eq74455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq74455
  have eq74582 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (τ (σ X0))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (M.op (M.op x y) x) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq74549 X0
       have i₂ := eq16 (M.op (M.op sF0 x) (τ (σ X0)))
       grind)
    | exact superpose eq16 eq74549
    | (have j0 := eq74549 X0
       grind)
    | exact resolve eq74549 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74549
  have eq74623 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (M.op (M.op x y) x) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq74582 X0
       have i₂ := eq16 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq16 eq74582
    | (have j0 := eq74582 X0
       grind)
    | exact resolve eq74582 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74582
  have eq74639 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op (M.op x y) x) X0) ∨ (τ (σ X0)) = (M.op (M.op (M.op x y) x) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq74623 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq74623
    | (have j0 := eq74623 X0
       grind)
    | exact resolve eq74623 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74623
  have eq74642 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ (k (M.op X0 X0) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have i₁ := eq74639 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq74639
    | (have j0 := eq74639 X0
       grind)
    | exact resolve eq74639 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74639
  have eq74645 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have j0 := eq74642 X0
       have j1 := eq64499 X0 X0
       grind)
    | (have r₁ := eq74642 x
       have r₂ := eq64499 x x
       grind)
    | exact resolve eq74642 eq64499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64499 eq74642
  have eq97526 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) x) X0) = (k (M.op (M.op (M.op x y) x) X0) (M.op X2 X0)) ∨ (M.op X2 X0) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq3415 X2 X2
       have i₂ := eq304 (M.op (M.op sF0 x) X2) (M.op sF0 x) X2
       grind)
    | exact superpose eq304 eq3415
    | (have j0 := eq3415 X0 X2
       grind)
    | exact resolve eq3415 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415
  have eq97527 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op x y) x) X0) ∨ (M.op (M.op (M.op x y) x) X0) = (k (M.op (M.op (M.op x y) x) X0) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq97526 X2 x
       have i₂ := eq304 (M.op (M.op sF0 x) X2) x X2
       grind)
    | exact superpose eq304 eq97526
    | (have j0 := eq97526 X0 X2
       grind)
    | exact resolve eq97526 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97526
  have eq97528 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) x) X0) = (k (M.op (M.op (M.op x y) x) X0) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq97527 X0 X2
       have j1 := eq2458 X0 X2 (M.op (M.op (M.op x y) x) X0)
       grind)
    | (have r₁ := eq97527 X0 X2
       have r₂ := eq2458 X0 X2 x
       grind)
    | (have r₁ := eq97527 X0 (M.op (M.op x y) x)
       have r₂ := eq2458 X0 (M.op (M.op x y) x) x
       grind)
    | exact resolve eq97527 eq2458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2458 eq97527
  have eq103807 : (σ (k (k y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq61282 eq193
    | exact resolve eq193 eq61282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq103808 : (σ (k (k y y) y)) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | (have i₁ := eq103807
       have i₂ := eq74645 sF3
       grind)
    | exact superpose eq74645 eq103807
    | exact resolve eq103807 eq74645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103807
  have eq107325 : (k (k y y) y) = (τ (M.op (M.op (M.op x y) x) (σ y))) := by
    first
    | (have i₁ := eq16 (k (k y y) y)
       have i₂ := eq103808
       grind)
    | exact superpose eq103808 eq16
    | exact resolve eq16 eq103808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103808
  have eq111217 : ∀ X0 : G, (k (k y y) y) = (τ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq309 eq107325
    | exact resolve eq107325 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq107325
  have eq115403 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq61094 eq87
    | exact resolve eq87 eq61094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq115806 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq61282 eq122
    | exact resolve eq122 eq61282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq117005 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq61464 eq162
    | exact resolve eq162 eq61464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq117007 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq61464 eq165
    | exact resolve eq165 eq61464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq151830 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq115403
       grind)
    | exact superpose eq115403 eq16
    | exact resolve eq16 eq115403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115403
  have eq151901 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq61103 eq151830
    | exact resolve eq151830 eq61103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151830
  have eq151913 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq151901
       have r₂ := eq13 x x
       grind)
    | exact resolve eq151901 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151901
  have eq151915 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq151913
       grind)
    | exact superpose eq151913 eq44
    | exact resolve eq44 eq151913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq151966 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq61094 eq151915
    | exact resolve eq151915 eq61094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61094 eq151915
  have eq152006 : (k (M.op (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) := by
    first
    | (have i₁ := eq40 (M.op x x)
       have i₂ := eq151966
       grind)
    | exact superpose eq151966 eq40
    | exact resolve eq40 eq151966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq152074 : (σ (M.op (M.op x y) x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq152006
       have i₂ := eq38980
       grind)
    | exact superpose eq38980 eq152006
    | exact resolve eq152006 eq38980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38980 eq152006
  have eq152086 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq39077 eq152074
    | exact resolve eq152074 eq39077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39077 eq152074
  have eq152754 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq115806
       grind)
    | exact superpose eq115806 eq16
    | exact resolve eq16 eq115806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115806
  have eq152827 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq61292 eq152754
    | exact resolve eq152754 eq61292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61292 eq152754
  have eq152836 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq152827
       have r₂ := eq13 y y
       grind)
    | exact resolve eq152827 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152827
  have eq152837 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq152836
       grind)
    | exact superpose eq152836 eq97
    | exact resolve eq97 eq152836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq152844 : ∀ X0 : G, (k (M.op y y) y) = (τ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq111217 X0
       have i₂ := eq152836
       grind)
    | exact superpose eq152836 eq111217
    | exact resolve eq111217 eq152836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111217 eq152836
  have eq152892 : ∀ X0 : G, (M.op (M.op (M.op x y) x) y) = (τ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq152844 X0
       have i₂ := eq74645 y
       grind)
    | exact superpose eq74645 eq152844
    | exact resolve eq152844 eq74645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74645 eq152844
  have eq152894 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq61282 eq152837
    | exact resolve eq152837 eq61282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61282 eq152837
  have eq153326 : ∀ X0 X1 : G, (σ (M.op X1 (M.op x y))) = (σ (τ (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq152892 eq62757
    | exact resolve eq62757 eq152892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62757 eq152892
  have eq153551 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (σ (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq153326 X0 X1
       have i₂ := eq15 (M.op X0 sF4)
       grind)
    | exact superpose eq15 eq153326
    | exact resolve eq153326 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153326
  have eq155877 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq117007 eq16
    | exact resolve eq16 eq117007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117007
  have eq155971 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq61476 eq155877
    | exact resolve eq155877 eq61476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61476 eq155877
  have eq155985 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq155971
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq155971 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155971
  have eq155991 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq155985 eq141
    | exact resolve eq141 eq155985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq156045 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq61464 eq155991
    | exact resolve eq155991 eq61464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61464 eq155991
  have eq156071 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq224 eq156045
    | exact resolve eq156045 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq156075 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq153551 eq156045
    | exact resolve eq156045 eq153551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153551 eq156045
  have eq156206 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq288 eq156075
    | exact resolve eq156075 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq157166 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq156071 eq4521
    | exact resolve eq4521 eq156071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4521
  have eq157279 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq156071 eq157166
    | exact resolve eq157166 eq156071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156071 eq157166
  have eq157476 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ (M.op x y))) := by
    first
    | exact superpose eq97528 eq157279
    | exact resolve eq157279 eq97528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97528
  have eq157673 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq304 eq157476
    | exact resolve eq157476 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq157476
  have eq175419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq175419
    | exact resolve eq175419 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175419
  have eq175442 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq175431
       have r₂ := eq28
       grind)
    | exact resolve eq175431 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175431
  have eq175447 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq175442 eq61103
    | exact resolve eq61103 eq175442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175442
  have eq175651 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq175447
       have i₂ := eq151913
       grind)
    | exact superpose eq151913 eq175447
    | exact resolve eq175447 eq151913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175447
  have eq175678 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq175651
    | exact resolve eq175651 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175651
  have eq175679 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq175678
  have eq175692 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq175679 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq175679
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq175679
       grind)
    | exact resolve eq13 eq175679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175679
  have eq175762 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq175692
  have eq175859 : (τ (σ x)) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq175762 eq106
    | exact resolve eq106 eq175762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq175860 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq175762 eq108
    | exact resolve eq108 eq175762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175762
  have eq175879 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq175860
  have eq175887 : y = (M.op x x) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq175859
    | exact resolve eq175859 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq175859
  have eq175939 : (M.op y x) = (k y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq111 x x
       have i₂ := eq175879
       grind)
    | exact superpose eq175879 eq111
    | exact resolve eq111 eq175879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175879
  have eq176004 : (M.op y x) = (k y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq175939
  have eq176057 : (M.op y x) = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq176004
       have r₂ := eq13 y x
       grind)
    | exact resolve eq176004 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176004
  have eq176109 : (σ (M.op y x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq176057
       grind)
    | exact superpose eq176057 eq96
    | exact resolve eq96 eq176057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176267 : (k (k (σ y) (σ x)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (M.op y x) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq117005 (M.op y x)
       have i₂ := eq176109
       grind)
    | exact superpose eq176109 eq117005
    | exact resolve eq117005 eq176109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117005 eq176109
  have eq176272 : (k (k (σ y) (σ x)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (M.op y x) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq155985 eq176267
    | exact resolve eq176267 eq155985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155985 eq176267
  have eq176280 : (σ (M.op (M.op (M.op x y) x) y)) = (k (k (σ y) (σ x)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2648 eq176272
    | exact resolve eq176272 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq176272
  have eq176281 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq157279 eq176280
    | exact resolve eq176280 eq157279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157279 eq176280
  have eq176498 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op X0 (M.op (σ x) (σ y))) y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq5851 eq176281
    | exact resolve eq176281 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5851 eq176281
  have eq177193 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq156075 eq176498
    | exact resolve eq176498 eq156075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176498
  have eq178802 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (σ (M.op (M.op X0 (M.op (σ x) (σ y))) y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq156075 eq177193
    | exact resolve eq177193 eq156075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156075 eq177193
  have eq179080 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (σ (M.op (M.op y X0) y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq178802 y
       have i₂ := eq499 X0 y sF4
       grind)
    | exact superpose eq499 eq178802
    | exact resolve eq178802 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178802
  have eq291364 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq151966
       have i₂ := eq175887
       grind)
    | exact superpose eq175887 eq151966
    | exact resolve eq151966 eq175887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151966
  have eq291409 : (M.op y x) = (k y x) ∨ x = (M.op y x) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq111 x x
       have i₂ := eq175887
       grind)
    | exact superpose eq175887 eq111
    | exact resolve eq111 eq175887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175887
  have eq291477 : (M.op y x) = (k y x) ∨ x = (M.op y x) ∨ x = (k y x) := by grind
  clear eq291409
  have eq291533 : (M.op y x) = (k y x) ∨ x = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq291477
       have r₂ := eq13 y x
       grind)
    | exact resolve eq291477 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291477
  have eq291561 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq291364
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq291364
    | exact resolve eq291364 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq291364
  have eq291607 : x ≠ (M.op y x) ∨ x = (k y x) := by grind
  clear eq291533
  have eq293752 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq291561
       have r₂ := eq291607
       grind)
    | exact resolve eq291561 eq291607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291561 eq291607
  have eq293756 : (τ (σ y)) = (k x x) ∨ x = (k y x) := by
    first
    | exact superpose eq293752 eq61103
    | exact resolve eq61103 eq293752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61103
  have eq293766 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (σ y)) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq293752 eq60
    | exact resolve eq60 eq293752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq293752
  have eq293940 : (τ (σ y)) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq293756
       have i₂ := eq151913
       grind)
    | exact superpose eq151913 eq293756
    | exact resolve eq293756 eq151913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151913 eq293756
  have eq293968 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq30 eq293940
    | exact resolve eq293940 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq293940
  have eq293984 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq59 X0 x
       have i₂ := eq293968
       grind)
    | exact superpose eq293968 eq59
    | exact resolve eq59 eq293968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293968
  have eq294335 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (k y x) ∨ x = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq293766 eq293766
    | exact resolve eq293766 eq293766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293766
  have eq294841 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (k y x) := by
    intro X0 X1
    first
    | (have j0 := eq294335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294335
  have eq295718 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (k y x) ∨ x = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq293984 eq293984
    | exact resolve eq293984 eq293984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293984
  have eq296313 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (k y x) := by
    intro X0 X1
    first
    | (have j0 := eq295718 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295718
  have eq300164 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq27 eq294841
    | (have j0 := eq294841 X0 (σ x)
       grind)
    | exact resolve eq294841 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294841
  have eq309603 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq296313 X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq296313
    | (have j0 := eq296313 X0 x
       grind)
    | exact resolve eq296313 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296313
  have eq311148 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq152894
       have i₂ := eq309603 y
       grind)
    | exact superpose eq309603 eq152894
    | exact resolve eq152894 eq309603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152894 eq309603
  have eq311188 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq21 eq311148
    | exact resolve eq311148 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311148
  have eq312720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq311188 eq300164
    | exact resolve eq300164 eq311188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300164 eq311188
  have eq312824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq312720
  have eq312889 : x = (k y x) := by
    first
    | (have r₁ := eq312824
       have r₂ := eq28
       grind)
    | exact resolve eq312824 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312824
  have eq312966 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq312889
       have i₂ := eq176057
       grind)
    | exact superpose eq176057 eq312889
    | exact resolve eq312889 eq176057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176057
  have eq312973 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq312889
       grind)
    | exact superpose eq312889 eq96
    | exact resolve eq96 eq312889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq312889
  have eq313017 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq312973
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq312973
    | exact resolve eq312973 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312973
  have eq313147 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq179080 x X0
       have i₂ := eq312966
       grind)
    | exact superpose eq312966 eq179080
    | exact resolve eq179080 eq312966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179080
  have eq313151 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq59 X0 y
       have i₂ := eq312966
       grind)
    | exact superpose eq312966 eq59
    | exact resolve eq59 eq312966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq313228 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq313147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313147
  have eq313289 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq313228 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq313228
    | (have j0 := eq313228 X0
       grind)
    | exact resolve eq313228 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq313228
  have eq313316 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq21 eq313289
    | (have j0 := eq313289 X0
       grind)
    | exact resolve eq313289 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq313289
  have eq328862 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq313151 X0
       have i₂ := eq313151 sF0
       grind)
    | exact superpose eq313151 eq313151
    | exact resolve eq313151 eq313151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313151
  have eq329336 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq328862 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328862
  have eq356801 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq312966
       have i₂ := eq329336 X0 y
       grind)
    | (have i₁ := eq312966
       have i₂ := eq329336 y X0
       grind)
    | exact superpose eq329336 eq312966
    | exact resolve eq312966 eq329336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312966 eq329336
  have eq356895 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq356801 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356801
  have eq357696 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq152086
       have i₂ := eq356895 sF0
       grind)
    | exact superpose eq356895 eq152086
    | exact resolve eq152086 eq356895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152086 eq356895
  have eq357786 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq357696
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq357696
    | exact resolve eq357696 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq357696
  have eq358259 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq357786 eq328
    | exact resolve eq328 eq357786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq357786
  have eq358412 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq27 eq358259
    | (have j0 := eq358259 X0
       grind)
    | exact resolve eq358259 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358259
  have eq359916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq358412 eq313316
    | exact resolve eq313316 eq358412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313316 eq358412
  have eq360231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq359916
  have eq360434 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq360231
       have r₂ := eq28
       grind)
    | exact resolve eq360231 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360231
  have eq360632 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq360434 eq27
    | exact resolve eq27 eq360434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq360743 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq360434 eq313017
    | exact resolve eq313017 eq360434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313017 eq360434
  have eq361635 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq360743 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq360743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq360632 eq361635
    | exact resolve eq361635 eq360632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361635
  have eq361664 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq361652
       have r₂ := eq28
       grind)
    | exact resolve eq361652 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361652
  have eq394546 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq361664 eq111
    | exact resolve eq111 eq361664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq361664
  have eq394626 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq394546
  have eq394704 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq394626
       have r₂ := eq13 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq394626 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394626
  have eq394782 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq360743 eq394704
    | exact resolve eq394704 eq360743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360743 eq394704
  have eq394876 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq394782 eq157673
    | exact resolve eq157673 eq394782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157673
  have eq394905 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq394782 eq499
    | exact resolve eq499 eq394782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq395019 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq156206 eq394905
    | exact resolve eq394905 eq156206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156206 eq394905
  have eq395075 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq360632 eq395019
    | exact resolve eq395019 eq360632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360632 eq395019
  have eq430947 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq395075 eq394876
    | exact resolve eq394876 eq395075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394876 eq395075
  have eq431470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq430947 eq394782
    | exact resolve eq394782 eq430947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394782 eq430947
  have eq431479 : False := by grind
  exact eq431479

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq12 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq14 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq51
    | (have j0 := eq51 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq51 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq297
       have i₂ := eq51 y x
       grind)
    | exact superpose eq51 eq297
    | (have j1 := eq51 (σ x) (σ y)
       grind)
    | (have r₁ := eq297
       have r₂ := eq51 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq297
       have r₂ := eq51 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq297 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq297
  have eq332 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq327
  have eq419 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq332
       grind)
    | exact superpose eq332 eq16
    | exact resolve eq16 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq433 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq619 : ∀ X0 : G, (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq41 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq620 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq619 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq619
    | exact resolve eq619 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq624 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq620 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq620
    | exact resolve eq620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq650 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq624 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq624
    | exact resolve eq624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq706 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq433 X0
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq433
    | exact resolve eq433 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq650
  have eq6001 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq419
       have r₂ := eq706 x
       grind)
    | exact resolve eq419 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq6003 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6001
       grind)
    | exact superpose eq6001 eq10
    | exact resolve eq10 eq6001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6001
  have eq6040 : x = y := by
    first
    | (have i₁ := eq6003
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6003
    | exact resolve eq6003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003
  have eq6042 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6040
       grind)
    | exact superpose eq6040 eq16
    | exact resolve eq16 eq6040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6040
  have eq6043 : False := by grind
  exact eq6043

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyy_y_pxx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq22
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X2) X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 X3) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op (M.op X2 X2) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X2 X2) X3 X4 X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq62 (M.op X1 X2) X1 X2 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq62 X0 X0 X2 X1
       grind)
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq62 X0 X1 X2 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X3 X4) (M.op X2 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq87 X3 X4 (M.op X2 X5) X0
       have i₂ := eq87 X2 X5 X0 X1
       grind)
    | (have i₁ := eq87 X3 X4 (M.op X2 X5) X0
       have i₂ := eq87 X0 X1 X2 X5
       grind)
    | exact superpose eq87 eq87
    | exact resolve eq87 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq196 (σ X0)
       grind)
    | exact superpose eq196 eq15
    | exact resolve eq15 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq196 (τ X0)
       grind)
    | exact superpose eq196 eq31
    | exact resolve eq31 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq208 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq201 X0
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq201
    | exact resolve eq201 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq210 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq199 X0
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq199
    | exact resolve eq199 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq199
  have eq230 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X0) X1 X2 (σ X0)
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq62
    | exact resolve eq62 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X1 X2 (σ X0) (σ X0)
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq87
    | exact resolve eq87 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X1) X2) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (τ X0) X1 X2 (τ X0)
       have i₂ := eq208 X0
       grind)
    | exact superpose eq208 eq62
    | exact resolve eq62 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (τ X0)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X1 X2 (τ X0) (τ X0)
       have i₂ := eq208 X0
       grind)
    | exact superpose eq208 eq87
    | exact resolve eq87 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (σ X0)) X1) X2) = (M.op (σ (σ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq230 (σ X0) X1 X2
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq230
    | exact resolve eq230 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq210 (M.op X0 X0)
       have i₂ := eq230 X0 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq230 eq210
    | exact resolve eq210 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq320 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq320 X0 X0
       have r₂ := eq12 X0 (σ X0)
       grind)
    | (have r₁ := eq320 X0 (σ X0)
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq320 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq347 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (τ X0)) = (M.op (τ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X1 (τ X0) (τ X0)
       have i₂ := eq208 X0
       grind)
    | exact superpose eq208 eq232
    | exact resolve eq232 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 X2 : G, (M.op (σ (σ (M.op X0 X0))) X1) = (M.op (M.op X1 X2) (σ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232 (σ X0) X1 X2
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq232
    | exact resolve eq232 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X2 X3) X4 X0 X1
       have i₂ := eq64 X2 X3 X1 X0
       grind)
    | exact superpose eq64 eq62
    | exact resolve eq62 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq710 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X2) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq87 X0 X2 (M.op X3 X4) X1
       have i₂ := eq64 X3 X4 X1 X0
       grind)
    | exact superpose eq64 eq87
    | exact resolve eq87 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq863 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 X3) (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq87 X0 X3 (M.op X4 X4) X1
       have i₂ := eq65 X4 X1 X0 X2
       grind)
    | exact superpose eq65 eq87
    | exact resolve eq87 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1130 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (M.op (M.op X2 X3) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq87 X2 X3 (M.op X4 X5) X0
       have i₂ := eq75 X4 X5 X0 X1 X2
       grind)
    | (have i₁ := eq87 X4 X1 (M.op X2 X2) X3
       have i₂ := eq75 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq75 eq87
    | exact resolve eq87 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2244 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (σ (M.op X0 X0))) = (M.op (M.op (M.op X2 X3) X4) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq707 X1 (σ X0) X2 X3 X4
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq707
    | exact resolve eq707 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq2970 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3142 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2970 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970
  have eq3942 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X5 X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq87 X0 X1 (M.op X2 X3) X5
       have i₂ := eq144 X2 X3 X5 X0 X4 X6
       grind)
    | (have i₁ := eq87 (M.op X2 X5) X1 X3 X4
       have i₂ := eq144 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq144 eq87
    | exact resolve eq87 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq5976 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq325 (τ X0) X1
       have i₂ := eq208 X0
       grind)
    | exact superpose eq208 eq325
    | (have j0 := eq325 (τ X0) X1
       grind)
    | exact resolve eq325 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq5982 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ X0)) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5976 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5976
    | (have j0 := eq5976 X0 X1
       grind)
    | exact resolve eq5976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5976
  have eq5985 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5982 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5982
    | (have j0 := eq5982 X0 X1
       grind)
    | exact resolve eq5982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5982
  have eq5986 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5985 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5985
    | (have j0 := eq5985 X0 X1
       grind)
    | exact resolve eq5985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5985
  have eq6109 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (σ (M.op X0 X0))) = (M.op (M.op X1 X2) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq710 X1 (σ X0) X2 X3 X4
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq710
    | exact resolve eq710 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6257 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (M.op X1 X3) (σ (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq710 X1 X2 X3 (σ X0) (σ X0)
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq710
    | exact resolve eq710 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6260 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (M.op X1 X3) (τ (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq710 X1 X2 X3 (τ X0) (τ X0)
       have i₂ := eq208 X0
       grind)
    | exact superpose eq208 eq710
    | exact resolve eq710 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6380 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (σ (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X1) (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq232 (M.op X0 X0) X4 X5
       have i₂ := eq710 X0 X0 X1 X2 X3
       grind)
    | (have i₁ := eq232 (M.op X3 X4) X1 X2
       have i₂ := eq710 X3 X1 X4 X3 X4
       grind)
    | exact superpose eq710 eq232
    | exact resolve eq232 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6382 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (τ (M.op X0 X0))) = (M.op (τ (M.op (M.op X0 X1) (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq247 (M.op X0 X0) X4 X5
       have i₂ := eq710 X0 X0 X1 X2 X3
       grind)
    | (have i₁ := eq247 (M.op X3 X4) X1 X2
       have i₂ := eq710 X3 X1 X4 X3 X4
       grind)
    | exact superpose eq710 eq247
    | exact resolve eq247 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6791 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X2 X3)) = (M.op (M.op X1 X4) (σ (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq863 X1 X2 X3 X4 (σ X0)
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq863
    | exact resolve eq863 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7764 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (σ (M.op X0 X0)) X1) X2) = (M.op (M.op X2 X3) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1130 (σ X0) X1 X2 X3 X4 X5
       have i₂ := eq230 X0 (σ X0) X1
       grind)
    | exact superpose eq230 eq1130
    | exact resolve eq1130 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq13024 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (σ (σ (M.op X0 X2))) X3) X4) = (M.op (σ (σ (M.op (M.op X0 X0) (M.op X1 X1)))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq271 (M.op X0 X2) X3 X4
       have i₂ := eq710 X0 X1 X2 X0 X2
       grind)
    | (have i₁ := eq271 (M.op X1 X1) X1 X2
       have i₂ := eq710 X1 X1 X2 X3 X4
       grind)
    | exact superpose eq710 eq271
    | exact resolve eq271 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq13029 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (σ (σ (M.op X0 X0))) X3) X4) = (M.op (σ (σ (M.op (M.op X0 X0) (M.op X1 X2)))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq271 (M.op X0 X0) X3 X4
       have i₂ := eq863 X0 X1 X2 X0 X0
       grind)
    | (have i₁ := eq271 (M.op X2 X2) X1 X2
       have i₂ := eq863 X2 X2 X2 X3 X4
       grind)
    | exact superpose eq863 eq271
    | exact resolve eq271 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14904 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (σ (M.op X0 X4)) X5) X6) = (M.op (σ (M.op (M.op X0 X1) (M.op X2 X3))) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq230 (M.op X0 X4) X5 X6
       have i₂ := eq3942 X0 X4 X0 X4 X1 X2 X3
       grind)
    | (have i₁ := eq230 (M.op X0 X4) X5 X6
       have i₂ := eq3942 X0 X1 X2 X3 X4 X0 X4
       grind)
    | exact superpose eq3942 eq230
    | exact resolve eq230 eq3942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14905 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (σ (M.op (M.op X0 X1) (M.op X2 X3))) X4) = (M.op (M.op X4 X5) (σ (M.op X0 X6))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq232 (M.op X0 X6) X4 X5
       have i₂ := eq3942 X0 X6 X0 X6 X1 X2 X3
       grind)
    | (have i₁ := eq232 (M.op X0 X6) X4 X5
       have i₂ := eq3942 X0 X1 X2 X3 X6 X0 X6
       grind)
    | exact superpose eq3942 eq232
    | exact resolve eq232 eq3942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14907 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (τ (M.op (M.op X0 X1) (M.op X2 X3))) X4) = (M.op (M.op X4 X5) (τ (M.op X0 X6))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq247 (M.op X0 X6) X4 X5
       have i₂ := eq3942 X0 X6 X0 X6 X1 X2 X3
       grind)
    | (have i₁ := eq247 (M.op X0 X6) X4 X5
       have i₂ := eq3942 X0 X1 X2 X3 X6 X0 X6
       grind)
    | exact superpose eq3942 eq247
    | exact resolve eq247 eq3942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16964 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (σ (M.op X0 X0))) X1) X2) = (M.op (M.op X2 X2) (σ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2244 X3 X2 (σ (σ X0)) x X1
       have i₂ := eq271 X0 x X1
       grind)
    | exact superpose eq271 eq2244
    | exact resolve eq2244 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq22169 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (σ (σ (M.op X0 X2))) X3) X4) = (M.op (σ (σ (M.op (M.op X0 X0) (σ (M.op X1 X1))))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq271 (M.op X0 X2) X3 X4
       have i₂ := eq6109 X1 X0 X2 X0 X2
       grind)
    | exact superpose eq6109 eq271
    | exact resolve eq271 eq6109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq6109
  have eq22657 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (M.op X2 X2)) = (M.op (M.op (τ (M.op X0 X0)) (σ X1)) (σ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6257 X3 (σ (M.op X1 X1)) X2 (τ X0)
       have i₂ := eq347 X0 X1
       grind)
    | exact superpose eq347 eq6257
    | exact resolve eq6257 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq6257
  have eq23216 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op (M.op X1 X1) (M.op X1 X1))) (M.op X2 X2)) = (M.op (M.op (τ (M.op X0 X0)) (σ X1)) (σ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22657 X0 X1 X2 X3
       have i₂ := eq230 (M.op X1 X1) (σ (M.op X1 X1)) (M.op X2 X2)
       grind)
    | exact superpose eq230 eq22657
    | exact resolve eq22657 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22657
  have eq23834 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ (M.op X0 X0)) (M.op X3 X4)) = (M.op (M.op (σ X0) X1) (σ (M.op X2 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq230 X0 (σ X0) (M.op X3 X4)
       have i₂ := eq6791 X2 (σ X0) X3 X4 X1
       grind)
    | exact superpose eq6791 eq230
    | exact resolve eq230 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26578 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X5 X6) (τ (M.op (σ (M.op X0 X0)) X1))) = (M.op (τ (M.op (M.op (M.op (σ (M.op X0 X0)) X1) X2) (M.op X3 X4))) X5) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq247 (M.op (σ (M.op X0 X0)) X1) X5 X6
       have i₂ := eq7764 X0 X1 (M.op (σ (M.op X0 X0)) X1) X2 X3 X4
       grind)
    | exact superpose eq7764 eq247
    | exact resolve eq247 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq32875 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142
  have eq32885 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32875 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq32875 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq32875 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq32875 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32875
  have eq33540 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0
       have i₂ := eq32885 X1 (σ X0)
       grind)
    | exact superpose eq32885 eq210
    | (have j1 := eq32885 X1 (σ X0)
       grind)
    | exact resolve eq210 eq32885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq33576 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq32885 (τ X1) X0
       grind)
    | exact superpose eq32885 eq17
    | (have j1 := eq32885 X0 X0
       grind)
    | exact resolve eq17 eq32885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq32885
  have eq35492 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33576 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33576
    | (have j0 := eq33576 X1 X1
       grind)
    | exact resolve eq33576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33576
  have eq36076 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35492 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35492
    | (have j0 := eq35492 X0 X1
       grind)
    | exact resolve eq35492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35492
  have eq39107 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq33540 X0 X1
       grind)
    | exact superpose eq33540 eq10
    | (have j1 := eq33540 X0 X1
       grind)
    | exact resolve eq10 eq33540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33540
  have eq39141 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39107 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39107
    | (have j0 := eq39107 X0 X1
       grind)
    | exact resolve eq39107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39107
  have eq39596 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq39141 X0 (σ X1)
       grind)
    | exact superpose eq39141 eq15
    | (have j1 := eq39141 X0 X1
       grind)
    | exact resolve eq15 eq39141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39141
  have eq40572 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36076 X1 X0
       have i₂ := eq39596 X0 X1
       grind)
    | exact superpose eq39596 eq36076
    | (have j0 := eq36076 X0 X0
       have j1 := eq39596 X0 X1
       grind)
    | exact resolve eq36076 eq39596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36076 eq39596
  have eq40921 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40572 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40572
  have eq43445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40921 x y
       grind)
    | exact superpose eq40921 eq16
    | (have j1 := eq40921 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq40921 x y
       grind)
    | exact resolve eq16 eq40921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40921
  have eq43986 : x = (M.op x x) := by grind
  clear eq43445
  have eq44082 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 x X0 X1
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq232
    | exact resolve eq232 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44127 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq5986 x X0
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq5986
    | (have j0 := eq5986 x X0
       grind)
    | (have r₁ := eq5986 x x
       have r₂ := eq43986
       grind)
    | exact resolve eq5986 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5986
  have eq44137 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (τ (M.op X2 X2))) = (M.op (M.op X0 X0) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6260 X2 X0 x X1
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq6260
    | exact resolve eq6260 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6260
  have eq44161 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1 x x
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq87
    | exact resolve eq87 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq44217 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3942 X0 X1 X2 X3 X4 x x
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq3942
    | exact resolve eq3942 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3942
  have eq44224 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ (M.op X2 X2))) = (M.op (M.op X0 X0) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6791 X2 X0 x x X1
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq6791
    | exact resolve eq6791 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6791
  have eq44228 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (M.op X0 X0)) X1) X2) = (M.op (M.op X2 X3) x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7764 X0 X1 X2 X3 x x
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq7764
    | exact resolve eq7764 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7764
  have eq44236 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq44127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44127
  have eq44242 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op x X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44217 X0 X1 X2 X3 x
       have i₂ := eq44161 X0 x
       grind)
    | exact superpose eq44161 eq44217
    | exact resolve eq44217 eq44161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44217
  have eq44245 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44228 X0 X1 X2 x
       have i₂ := eq44161 X2 x
       grind)
    | exact superpose eq44161 eq44228
    | exact resolve eq44228 eq44161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44228
  have eq44246 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ (M.op X2 X2))) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44224 X0 X1 X2
       have i₂ := eq44161 X0 X0
       grind)
    | exact superpose eq44161 eq44224
    | exact resolve eq44224 eq44161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44224
  have eq44262 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (τ (M.op X2 X2))) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44137 X0 X1 X2
       have i₂ := eq44161 X0 X0
       grind)
    | exact superpose eq44161 eq44137
    | exact resolve eq44137 eq44161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44137 eq44161
  have eq44317 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ (M.op (M.op X0 X1) (M.op X2 X3))) X4) = (M.op x X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6380 X0 X1 X2 X3 X4 x
       have i₂ := eq44246 X4 x X0
       grind)
    | exact superpose eq44246 eq6380
    | exact resolve eq6380 eq44246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6380
  have eq44507 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (σ (M.op X0 X0))) X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16964 X0 X1 X2 x
       have i₂ := eq44246 X2 X2 x
       grind)
    | exact superpose eq44246 eq16964
    | exact resolve eq16964 eq44246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16964
  have eq44531 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (σ (σ (M.op X0 X2))) X3) X4) = (M.op (σ (σ (M.op x X0))) X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq22169 X0 x X2 X3 X4
       have i₂ := eq44246 X0 X0 x
       grind)
    | exact superpose eq44246 eq22169
    | exact resolve eq22169 eq44246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22169
  have eq44802 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq294 X0 x
       have i₂ := eq44246 (σ X0) x X0
       grind)
    | exact superpose eq44246 eq294
    | exact resolve eq294 eq44246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq44860 : ∀ X0 X3 X4 : G, (M.op (σ (M.op X0 X0)) (M.op X3 X4)) = (M.op x (σ X0)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq23834 X0 x x X3 X4
       have i₂ := eq44246 (σ X0) x x
       grind)
    | exact superpose eq44246 eq23834
    | exact resolve eq23834 eq44246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23834
  have eq44943 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X1 X1) (M.op X1 X1))) (M.op X2 X2)) = (M.op x (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23216 X0 X1 X2 x
       have i₂ := eq44246 (τ (M.op X0 X0)) (σ X1) x
       grind)
    | exact superpose eq44246 eq23216
    | exact resolve eq23216 eq44246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23216 eq44246
  have eq45132 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X5 X6) (τ (M.op (σ (M.op X0 X0)) X1))) = (M.op (τ (M.op (M.op x X2) (M.op X3 X4))) X5) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq26578 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq44245 X0 X1 X2
       grind)
    | exact superpose eq44245 eq26578
    | exact resolve eq26578 eq44245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26578 eq44245
  have eq45780 : ∀ X0 X1 X2 X3 X4 : G, (M.op (τ (M.op (M.op X0 X1) (M.op X2 X3))) X4) = (M.op x X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6382 X0 X1 X2 X3 X4 x
       have i₂ := eq44262 X4 x X0
       grind)
    | exact superpose eq44262 eq6382
    | exact resolve eq6382 eq44262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6382 eq44262
  have eq46380 : ∀ X0 X1 X2 : G, (M.op x (τ (M.op X0 X0))) = (M.op (M.op x (σ X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44943 X0 X1 X2
       have i₂ := eq44802 X1
       grind)
    | exact superpose eq44802 eq44943
    | exact resolve eq44943 eq44802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44802 eq44943
  have eq46653 : ∀ X0 X1 X2 X4 : G, (M.op (σ (σ (M.op (M.op X0 X0) (M.op X1 X2)))) X4) = (M.op x X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq13029 X0 X1 X2 x X4
       have i₂ := eq44507 X0 x X4
       grind)
    | exact superpose eq44507 eq13029
    | exact resolve eq13029 eq44507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13029 eq44507
  have eq46817 : ∀ X0 X4 X5 X6 : G, (M.op (M.op (σ (M.op X0 X4)) X5) X6) = (M.op x X6) := by
    intro X0 X4 X5 X6
    first
    | (have i₁ := eq14904 X0 x x x X4 X5 X6
       have i₂ := eq44317 X0 x x x X6
       grind)
    | exact superpose eq44317 eq14904
    | exact resolve eq14904 eq44317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14904
  have eq46818 : ∀ X0 X4 X5 X6 : G, (M.op (M.op X4 X5) (σ (M.op X0 X6))) = (M.op x X4) := by
    intro X0 X4 X5 X6
    first
    | (have i₁ := eq14905 X0 x x x X4 X5 X6
       have i₂ := eq44317 X0 x x x X4
       grind)
    | exact superpose eq44317 eq14905
    | exact resolve eq14905 eq44317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14905 eq44317
  have eq47143 : ∀ X0 X1 X5 X6 : G, (M.op (M.op X5 X6) (τ (M.op (σ (M.op X0 X0)) X1))) = (M.op (τ (M.op x x)) X5) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq45132 X0 X1 x x x X5 X6
       have i₂ := eq44242 x x x x
       grind)
    | exact superpose eq44242 eq45132
    | exact resolve eq45132 eq44242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45132
  have eq47330 : ∀ X0 X4 X5 X6 : G, (M.op (M.op X4 X5) (τ (M.op X0 X6))) = (M.op x X4) := by
    intro X0 X4 X5 X6
    first
    | (have i₁ := eq14907 X0 x x x X4 X5 X6
       have i₂ := eq45780 X0 x x x X4
       grind)
    | exact superpose eq45780 eq14907
    | exact resolve eq14907 eq45780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907 eq45780
  have eq47427 : ∀ X0 : G, (M.op x x) = (M.op x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq46380 X0 x x
       have i₂ := eq44242 x (σ x) x x
       grind)
    | exact superpose eq44242 eq46380
    | exact resolve eq46380 eq44242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44242 eq46380
  have eq47587 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (σ (σ (M.op X0 X2))) X3) X4) = (M.op x X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq13024 X0 x X2 X3 X4
       have i₂ := eq46653 X0 x x X4
       grind)
    | exact superpose eq46653 eq13024
    | exact resolve eq13024 eq46653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13024 eq46653
  have eq47911 : ∀ X0 X1 X5 X6 : G, (M.op (M.op X5 X6) (τ (M.op (σ (M.op X0 X0)) X1))) = (M.op (τ x) X5) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq47143 X0 X1 X5 X6
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq47143
    | exact resolve eq47143 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47143
  have eq48123 : ∀ X0 : G, x = (M.op x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq47427 X0
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq47427
    | exact resolve eq47427 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47427
  have eq48273 : ∀ X0 X4 : G, (M.op x X4) = (M.op (σ (σ (M.op x X0))) X4) := by
    intro X0 X4
    first
    | (have i₁ := eq44531 X0 x x X4
       have i₂ := eq47587 X0 x x X4
       grind)
    | exact superpose eq47587 eq44531
    | exact resolve eq44531 eq47587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44531 eq47587
  have eq48310 : ∀ X5 : G, (M.op x X5) = (M.op (τ x) X5) := by
    intro X5
    first
    | (have i₁ := eq47911 x x X5 x
       have i₂ := eq47330 (σ (M.op x x)) X5 x x
       grind)
    | exact superpose eq47330 eq47911
    | exact resolve eq47911 eq47330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47911
  have eq49726 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (k (σ (M.op X0 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 (σ (M.op X0 X0)) X1
       have i₂ := eq44236 (σ (M.op X0 X0))
       grind)
    | exact superpose eq44236 eq232
    | exact resolve eq232 eq44236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq49730 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq208 X0
       have i₂ := eq44236 (τ X0)
       grind)
    | exact superpose eq44236 eq208
    | exact resolve eq208 eq44236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49733 : ∀ X0 X1 : G, (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 X1 (τ (M.op X0 X0))
       have i₂ := eq44236 (τ (M.op X0 X0))
       grind)
    | exact superpose eq44236 eq245
    | exact resolve eq245 eq44236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq44236
  have eq49769 : ∀ X0 : G, (M.op x (τ X0)) = (k (τ (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq49733 X0 x
       have i₂ := eq47330 X0 (τ X0) x X0
       grind)
    | exact superpose eq47330 eq49733
    | exact resolve eq49733 eq47330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47330 eq49733
  have eq49773 : ∀ X0 : G, (M.op x (σ X0)) = (k (σ (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq49726 X0 x
       have i₂ := eq46817 X0 X0 x (σ X0)
       grind)
    | exact superpose eq46817 eq49726
    | exact resolve eq49726 eq46817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46817 eq49726
  have eq50555 : x = (M.op x (τ x)) := by
    first
    | (have i₁ := eq48123 x
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq48123
    | exact resolve eq48123 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48123
  have eq50908 : (τ (M.op x x)) = (M.op x (τ x)) := by
    first
    | (have i₁ := eq208 x
       have i₂ := eq48310 (τ x)
       grind)
    | exact superpose eq48310 eq208
    | exact resolve eq208 eq48310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq50936 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (σ (τ x)))) = (M.op (σ (σ (M.op x (τ x)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq368 (τ x) X0 X1
       have i₂ := eq48310 (τ x)
       grind)
    | exact superpose eq48310 eq368
    | exact resolve eq368 eq48310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq48310
  have eq51109 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) (σ (σ (τ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50936 X0 X1
       have i₂ := eq48273 (τ x) X0
       grind)
    | exact superpose eq48273 eq50936
    | exact resolve eq50936 eq48273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48273 eq50936
  have eq51130 : x = (τ (M.op x x)) := by
    first
    | (have i₁ := eq50908
       have i₂ := eq50555
       grind)
    | exact superpose eq50555 eq50908
    | exact resolve eq50908 eq50555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50555 eq50908
  have eq51185 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq51109 X0 X1
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq51109
    | exact resolve eq51109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51109
  have eq51201 : x = (τ x) := by
    first
    | (have i₁ := eq51130
       have i₂ := eq43986
       grind)
    | exact superpose eq43986 eq51130
    | exact resolve eq51130 eq43986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43986 eq51130
  have eq51242 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq51185 X0 x
       have i₂ := eq44082 X0 x
       grind)
    | exact superpose eq44082 eq51185
    | exact resolve eq51185 eq44082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44082 eq51185
  have eq51295 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51242 (σ y)
       grind)
    | exact superpose eq51242 eq16
    | exact resolve eq16 eq51242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51242
  have eq51319 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq18 x X0
       have i₂ := eq51201
       grind)
    | exact superpose eq51201 eq18
    | exact resolve eq18 eq51201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq51201
  have eq51373 : ∀ X0 : G, (M.op x (σ X0)) = (σ (k (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq49773 X0
       have i₂ := eq51319 (M.op X0 X0)
       grind)
    | exact superpose eq51319 eq49773
    | exact resolve eq49773 eq51319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49773 eq51319
  have eq54951 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X0) (M.op X1 X2))) = (k (τ (M.op X0 X0)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49730 (M.op X0 X0)
       have i₂ := eq863 X0 X1 X2 X0 X0
       grind)
    | (have i₁ := eq49730 (M.op X2 X2)
       have i₂ := eq863 X2 X2 X2 x x
       grind)
    | exact superpose eq863 eq49730
    | exact resolve eq49730 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq54954 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X1))) = (k (τ (M.op X0 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq49730 (M.op X0 X1)
       have i₂ := eq66 X0 X1 (M.op X0 X1)
       grind)
    | (have i₁ := eq49730 (M.op X0 X0)
       have i₂ := eq66 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq66 eq49730
    | exact resolve eq49730 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq54980 : ∀ X0 X1 : G, (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = (k (τ (M.op (σ X0) X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq49730 (M.op (σ X0) X1)
       have i₂ := eq230 X0 X1 (M.op (σ X0) X1)
       grind)
    | exact superpose eq230 eq49730
    | exact resolve eq49730 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54988 : ∀ X0 X1 : G, (τ (M.op (M.op (σ X0) X1) (σ (M.op X0 X0)))) = (k (τ (σ (M.op X0 X0))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq49730 (σ (M.op X0 X0))
       have i₂ := eq230 X0 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq230 eq49730
    | exact resolve eq49730 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq49730
  have eq55143 : ∀ X0 X1 : G, (τ (M.op (M.op (σ X0) X1) (σ (M.op X0 X0)))) = (k (M.op X0 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq54988 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq54988
    | exact resolve eq54988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54988
  have eq55151 : ∀ X0 X1 : G, (τ (M.op x (σ X0))) = (k (τ (M.op (σ X0) X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq54980 X0 X1
       have i₂ := eq44860 X0 (σ X0) X1
       grind)
    | exact superpose eq44860 eq54980
    | exact resolve eq54980 eq44860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44860 eq54980
  have eq55173 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X0) (M.op X1 X2))) = (M.op x (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54951 X0 X1 X2
       have i₂ := eq49769 X0
       grind)
    | exact superpose eq49769 eq54951
    | exact resolve eq54951 eq49769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49769 eq54951
  have eq55203 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (M.op X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq55143 X0 x
       have i₂ := eq46818 X0 (σ X0) x X0
       grind)
    | exact superpose eq46818 eq55143
    | exact resolve eq55143 eq46818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46818 eq55143
  have eq55231 : ∀ X0 X1 : G, (M.op x (τ X0)) = (k (τ (M.op X0 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq54954 X0 X1
       have i₂ := eq55173 X0 X0 X1
       grind)
    | exact superpose eq55173 eq54954
    | exact resolve eq54954 eq55173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54954 eq55173
  have eq55289 : ∀ X0 : G, (τ (M.op x (σ X0))) = (M.op x (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq55151 X0 x
       have i₂ := eq55231 (σ X0) x
       grind)
    | exact superpose eq55231 eq55151
    | exact resolve eq55151 eq55231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55151 eq55231
  have eq55319 : ∀ X0 : G, (M.op x X0) = (τ (M.op x (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq55289 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55289
    | exact resolve eq55289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55289
  have eq55350 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq55203 X0
       have i₂ := eq55319 X0
       grind)
    | exact superpose eq55319 eq55203
    | exact resolve eq55203 eq55319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55203 eq55319
  have eq55358 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq51373 X0
       have i₂ := eq55350 X0
       grind)
    | exact superpose eq55350 eq51373
    | exact resolve eq51373 eq55350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51373 eq55350
  have eq55383 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq51295
       have i₂ := eq55358 y
       grind)
    | exact superpose eq55358 eq51295
    | (have r₁ := eq51295
       have r₂ := eq55358 y
       grind)
    | exact resolve eq51295 eq55358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51295 eq55358
  have eq55384 : False := by grind
  exact eq55384

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X1
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq50 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq50 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq51 X1 X0
       grind)
    | (have r₁ := eq59 X1 X0
       have r₂ := eq51 X0 X1
       grind)
    | exact resolve eq59 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq59
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq66
  have eq172 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq176 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq172 X1 X1
       have r₂ := eq69 X1 X1
       grind)
    | (have r₁ := eq172 X1 X0
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq172 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq172
  have eq281 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq176 (σ X1) (σ X0)
       grind)
    | exact superpose eq176 eq15
    | exact resolve eq15 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq176 X1 X0
       grind)
    | exact superpose eq176 eq281
    | exact resolve eq281 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq281
  have eq288 : False := by grind
  exact eq288

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_pyx_pyx_pxy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq62 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq62 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq62 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq65
  have eq85 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq95
  have eq1948 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq101 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq13
    | (have j0 := eq13 (σ X1) X1
       have j1 := eq101 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq101 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq101 X0 X1
       grind)
    | exact resolve eq13 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1985 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq1994 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1985 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq1985 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq1985 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1985
  have eq2004 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1994 X0 X1
       have j1 := eq85 X1 (σ X0)
       grind)
    | (have r₁ := eq1994 X0 X0
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq1994 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1994
  have eq2012 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2004 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2004
    | (have j0 := eq2004 X0 X1
       grind)
    | exact resolve eq2004 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2013 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2012 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012
  have eq2018 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2013 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2013
    | exact resolve eq2013 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2032 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2013 x y
       grind)
    | exact superpose eq2013 eq16
    | exact resolve eq16 eq2013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2230 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq2018 X0 (τ X1)
       grind)
    | exact superpose eq2018 eq17
    | exact resolve eq17 eq2018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2018
  have eq2266 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2230 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2230
    | exact resolve eq2230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2283 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2266 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2266
    | exact resolve eq2266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2320 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2032
       have i₂ := eq2283 x y
       grind)
    | exact superpose eq2283 eq2032
    | exact resolve eq2032 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032 eq2283
  have eq2321 : False := by grind
  exact eq2321

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  clear eq24
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X3) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq77 y x
       grind)
    | exact superpose eq77 eq74
    | (have j1 := eq77 x x
       grind)
    | exact resolve eq74 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq203 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq53 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54 eq203
    | exact resolve eq203 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op x X0)
       have i₂ := eq203 X0 (M.op x X0)
       grind)
    | (have i₁ := eq53 (M.op x y)
       have i₂ := eq203 X0 (M.op x y)
       grind)
    | exact superpose eq203 eq53
    | exact resolve eq53 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq351 X0
       have i₂ := eq14 x sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq351
    | exact resolve eq351 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq358 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq356 X0
       have i₂ := eq203 x sF0
       grind)
    | exact superpose eq203 eq356
    | exact resolve eq356 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq366 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 X0) x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X0 x X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq455 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq376 (M.op X0 X1) x
       have i₂ := eq376 X0 X1
       grind)
    | (have i₁ := eq376 (M.op x y) X0
       have i₂ := eq376 X0 X1
       grind)
    | exact superpose eq376 eq376
    | exact resolve eq376 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq455 sF0 X1
       have i₂ := eq14 sF0 x x
       grind)
    | (have i₁ := eq455 x X1
       have i₂ := eq14 x sF0 x
       grind)
    | exact superpose eq14 eq455
    | exact resolve eq455 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq488 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 X1
       have i₂ := eq203 x sF0
       grind)
    | exact superpose eq203 eq478
    | exact resolve eq478 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq594 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq377 (M.op X0 X1) x
       have i₂ := eq376 X0 X1
       grind)
    | (have i₁ := eq377 (M.op x y) X0
       have i₂ := eq376 X0 X1
       grind)
    | exact superpose eq376 eq377
    | exact resolve eq377 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq377 eq594
    | exact resolve eq594 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq717 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq1610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq109 eq77
    | (have j0 := eq77 x (σ x)
       grind)
    | exact resolve eq77 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1610
    | exact resolve eq1610 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1614 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1611
       have r₂ := eq27
       grind)
    | exact resolve eq1611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1618 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1614 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq1614
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1614
       grind)
    | exact resolve eq13 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1640 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1618 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618
  have eq1927 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1640 eq49
    | exact resolve eq49 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1640
  have eq2493 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1614 eq1927
    | exact resolve eq1927 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614 eq1927
  have eq2506 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq2493
  have eq2509 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq2506
    | exact resolve eq2506 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2506
  have eq2512 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq77 x x
       have i₂ := eq2509
       grind)
    | exact superpose eq2509 eq77
    | (have j0 := eq77 x x
       grind)
    | exact resolve eq77 eq2509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509
  have eq2513 : x = (M.op x x) := by grind
  clear eq2512
  have eq2542 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq376 x x
       have i₂ := eq2513
       grind)
    | exact superpose eq2513 eq376
    | exact resolve eq376 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq2550 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2542
       have i₂ := eq2513
       grind)
    | exact superpose eq2513 eq2542
    | exact resolve eq2542 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq2592 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2550 eq488
    | exact resolve eq488 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2595 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2550 eq2592
    | exact resolve eq2592 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2746 : ∀ X0 X1 : G, (M.op x x) ≠ (M.op (M.op (M.op x y) X0) x) ∨ (k (M.op x x) X1) = (M.op X1 (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x x) X1
       have i₂ := eq717 X0 x x
       grind)
    | (have i₁ := eq13 (M.op (M.op x y) X0) X1
       have i₂ := eq717 X0 (M.op (M.op x y) X0) x
       grind)
    | exact superpose eq717 eq13
    | (have j0 := eq13 (M.op x x) X1
       grind)
    | exact resolve eq13 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2759 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x y) X0) x) X2) X1) = (M.op (M.op (M.op x y) (M.op x x)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq366 (M.op x x) X1 X2
       have i₂ := eq717 X0 x x
       grind)
    | (have i₁ := eq366 (M.op (M.op x y) X0) X1 X2
       have i₂ := eq717 X0 (M.op (M.op x y) X0) X2
       grind)
    | exact superpose eq717 eq366
    | exact resolve eq366 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq2778 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X1) = (M.op (M.op (M.op (M.op (M.op x y) X0) x) X2) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq358 eq2759
    | exact resolve eq2759 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq2759
  have eq2791 : ∀ X1 : G, (M.op x x) ≠ (M.op (M.op x x) (M.op x y)) ∨ (k (M.op x x) X1) = (M.op X1 (M.op x x)) := by
    intro X1
    first
    | (have i₁ := eq2746 sF0 X1
       have i₂ := eq14 sF0 x x
       grind)
    | (have i₁ := eq2746 x X1
       have i₂ := eq14 x sF0 x
       grind)
    | exact superpose eq14 eq2746
    | (have j0 := eq2746 x X1
       grind)
    | exact resolve eq2746 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746
  have eq2846 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X1) = (M.op (M.op (M.op (M.op x x) (M.op x y)) X2) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq2778 sF0 X1 X2
       have i₂ := eq14 sF0 x X2
       grind)
    | (have i₁ := eq2778 X2 X1 X2
       have i₂ := eq14 x sF0 X2
       grind)
    | exact superpose eq14 eq2778
    | exact resolve eq2778 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq2858 : ∀ X1 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x x) X1) = (M.op X1 (M.op x x)) := by
    intro X1
    first
    | (have i₁ := eq2791 X1
       have i₂ := eq203 x sF0
       grind)
    | exact superpose eq203 eq2791
    | (have j0 := eq2791 X1
       grind)
    | exact resolve eq2791 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791
  have eq2883 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X1) = (M.op (M.op (M.op (M.op x y) x) X2) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq2846 X1 X1
       have i₂ := eq366 x X1 sF0
       grind)
    | exact superpose eq366 eq2846
    | exact resolve eq2846 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq2846
  have eq2895 : ∀ X1 : G, x ≠ (M.op x x) ∨ (k (M.op x x) X1) = (M.op X1 (M.op x x)) := by
    intro X1
    first
    | exact superpose eq2595 eq2858
    | (have j0 := eq2858 X1
       grind)
    | exact resolve eq2858 eq2595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq2910 : ∀ X1 X2 : G, (M.op (M.op x X2) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X1 X2
    first
    | exact superpose eq2550 eq2883
    | exact resolve eq2883 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550 eq2883
  have eq2919 : ∀ X1 : G, (k (M.op x x) X1) = (M.op X1 (M.op x x)) := by
    intro X1
    first
    | (have j0 := eq2895 X1
       grind)
    | (have r₁ := eq2895 X1
       have r₂ := eq2513
       grind)
    | exact resolve eq2895 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895
  have eq2925 : ∀ X1 X2 : G, (M.op x X1) = (M.op (M.op x X2) X1) := by
    intro X1 X2
    first
    | exact superpose eq2595 eq2910
    | exact resolve eq2910 eq2595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910
  have eq2933 : ∀ X1 : G, (k x X1) = (M.op X1 x) := by
    intro X1
    first
    | (have i₁ := eq2919 X1
       have i₂ := eq2513
       grind)
    | exact superpose eq2513 eq2919
    | exact resolve eq2919 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq2939 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq2925 X1 x
       have i₂ := eq203 x X1
       grind)
    | (have i₁ := eq2925 X1 y
       have i₂ := eq203 x X1
       grind)
    | exact superpose eq203 eq2925
    | (have j0 := eq2925 X1 y
       grind)
    | exact resolve eq2925 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925
  have eq2985 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2933 x
       grind)
    | exact superpose eq2933 eq43
    | exact resolve eq43 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2986 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2933 y
       grind)
    | exact superpose eq2933 eq44
    | exact resolve eq44 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq2991 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2985
       have i₂ := eq2513
       grind)
    | exact superpose eq2513 eq2985
    | exact resolve eq2985 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513 eq2985
  have eq2994 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2991
    | exact resolve eq2991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2991
  have eq3006 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2994 eq77
    | (have j0 := eq77 x (σ x)
       grind)
    | exact resolve eq77 eq2994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2994
  have eq3007 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3006
  have eq3040 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3007 eq377
    | exact resolve eq377 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq3041 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq3007 eq488
    | exact resolve eq488 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq3045 : x = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq2595 eq3041
    | exact resolve eq3041 eq2595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595 eq3041
  have eq3046 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3007 eq3040
    | exact resolve eq3040 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007 eq3040
  have eq3090 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq3045 eq630
    | exact resolve eq630 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3091 : (M.op (M.op x y) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq346 eq3090
    | exact resolve eq3090 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq3090
  have eq3096 : x = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq3045 eq3091
    | exact resolve eq3091 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045 eq3091
  have eq3117 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3046 eq630
    | exact resolve eq630 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq3118 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq3046 eq3117
    | exact resolve eq3117 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046 eq3117
  have eq3162 : x = (σ x) := by
    first
    | exact superpose eq3096 eq3118
    | exact resolve eq3118 eq3096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3096 eq3118
  have eq3163 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq3162 eq26
    | exact resolve eq26 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq5086 : (σ (M.op y x)) = (k x (σ y)) := by
    first
    | exact superpose eq3162 eq2986
    | exact resolve eq2986 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq5087 : (σ (M.op y x)) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq5086
       have i₂ := eq2933 sF3
       grind)
    | exact superpose eq2933 eq5086
    | exact resolve eq5086 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5086
  have eq5091 : (σ (k x (M.op y x))) = (k (σ x) (M.op (σ y) x)) := by
    first
    | (have i₁ := eq35 (M.op y x)
       have i₂ := eq5087
       grind)
    | exact superpose eq5087 eq35
    | exact resolve eq35 eq5087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq5087
  have eq5104 : (σ (k x (M.op y x))) = (k x (M.op (σ y) x)) := by
    first
    | exact superpose eq3162 eq5091
    | exact resolve eq5091 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162 eq5091
  have eq5105 : (σ (k x (M.op y x))) = (M.op (M.op (σ y) x) x) := by
    first
    | (have i₁ := eq5104
       have i₂ := eq2933 (M.op sF3 x)
       grind)
    | exact superpose eq2933 eq5104
    | exact resolve eq5104 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5104
  have eq5106 : (σ (k x (M.op y x))) = (M.op (M.op x x) (σ y)) := by
    first
    | (have i₁ := eq5105
       have i₂ := eq14 x sF3 x
       grind)
    | exact superpose eq14 eq5105
    | exact resolve eq5105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5105
  have eq5107 : (M.op (M.op x y) (σ y)) = (σ (k x (M.op y x))) := by
    first
    | (have i₁ := eq5106
       have i₂ := eq203 x sF3
       grind)
    | exact superpose eq203 eq5106
    | exact resolve eq5106 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq5108 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op y x) x)) := by
    first
    | (have i₁ := eq5107
       have i₂ := eq2933 (M.op y x)
       grind)
    | exact superpose eq2933 eq5107
    | exact resolve eq5107 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933 eq5107
  have eq5109 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq5108
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq5108
    | exact resolve eq5108 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5108
  have eq5110 : (σ (M.op (M.op x y) y)) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq5109
       have i₂ := eq203 x y
       grind)
    | exact superpose eq203 eq5109
    | exact resolve eq5109 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq5109
  have eq5111 : (σ (M.op (M.op x y) y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq2939 eq5110
    | exact resolve eq5110 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5110
  have eq5112 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3163 eq5111
    | exact resolve eq5111 eq3163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3163 eq5111
  have eq5113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2939 eq5112
    | exact resolve eq5112 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939 eq5112
  have eq5114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5113
    | exact resolve eq5113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5113
  have eq5115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5114
    | exact resolve eq5114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5114
  have eq5116 : False := by grind
  exact eq5116
