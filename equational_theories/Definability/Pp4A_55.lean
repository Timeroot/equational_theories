import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq32
    | exact resolve eq32 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32
  have eq63 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq17
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq67 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq67 (τ X0) X1
       grind)
    | exact superpose eq67 eq17
    | exact resolve eq17 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq80 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq80 (τ X0) X1
       grind)
    | exact superpose eq80 eq17
    | exact resolve eq17 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq131 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq70
    | (have j0 := eq70 X2 X2
       grind)
    | exact resolve eq70 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq234 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq88 (τ X0) X1
       grind)
    | exact superpose eq88 eq17
    | exact resolve eq17 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq236 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq234
    | exact resolve eq234 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq304 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq236 (τ X0) X1
       grind)
    | exact superpose eq236 eq17
    | exact resolve eq17 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq308 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq387 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))
       have i₂ := eq308 (τ X0) X1
       grind)
    | exact superpose eq308 eq17
    | exact resolve eq17 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq391 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq2349 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X0) (k X1 (σ X2))
       have i₂ := eq131 X1 X2 X0
       grind)
    | exact superpose eq131 eq19
    | (have j1 := eq131 X1 X2 X0
       grind)
    | exact resolve eq19 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq131
  have eq2350 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2349 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq17287 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2350 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2350
    | exact resolve eq2350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq17381 : ∀ X0 X1 X2 : G, (k (σ (k (τ X1) X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17287 X0 X1 X2
       have i₂ := eq18 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq18 eq17287
    | (have j0 := eq17287 X0 X1 X2
       grind)
    | exact resolve eq17287 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17287
  have eq17396 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17381 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq17381
    | (have j0 := eq17381 X0 X1 X2
       grind)
    | exact resolve eq17381 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq17381
  have eq17397 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17396 X0 X1 X2
       have j1 := eq12 (k X1 (σ X2)) X0
       grind)
    | (have r₁ := eq17396 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq17396 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17396
  have eq17428 : ∀ X0 X2 : G, (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq17397 X0 X0 (σ (σ (σ (σ (σ (M.op x x))))))
       have i₂ := eq391 X0 x
       grind)
    | exact superpose eq391 eq17397
    | exact resolve eq17397 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq17397
  have eq17941 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq17428 (σ X0) (σ X1)
       grind)
    | exact superpose eq17428 eq15
    | exact resolve eq15 eq17428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18023 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17941 X0 X1
       have i₂ := eq17428 X0 X1
       grind)
    | exact superpose eq17428 eq17941
    | exact resolve eq17941 eq17428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17428 eq17941
  have eq20428 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18023 x y
       grind)
    | exact superpose eq18023 eq16
    | (have r₁ := eq16
       have r₂ := eq18023 x y
       grind)
    | exact resolve eq16 eq18023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18023
  have eq20498 : False := by grind
  exact eq20498

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
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
  clear eq18
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X1 X0) X0
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq80 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X1) X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq85
    | exact resolve eq85 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq65 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq96 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq96 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq108 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (M.op X1 X1)
       have i₂ := eq87 X1 (σ X0)
       grind)
    | exact superpose eq87 eq30
    | exact resolve eq30 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq87 X1 (τ X0)
       grind)
    | exact superpose eq87 eq17
    | exact resolve eq17 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq111 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq109
    | exact resolve eq109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq108
    | exact resolve eq108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq139 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (τ (M.op X1 X1))
       have i₂ := eq112 (σ X0) X1
       grind)
    | exact superpose eq112 eq30
    | exact resolve eq30 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq145 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139
    | exact resolve eq139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq473 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq54 x y
       grind)
    | exact superpose eq54 eq94
    | (have j1 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq94
  have eq474 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq473
  have eq584 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74 x y
       have i₂ := eq474
       grind)
    | exact superpose eq474 eq74
    | exact resolve eq74 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq592 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74 (σ x) (σ y)
       have i₂ := eq584
       grind)
    | exact superpose eq584 eq74
    | exact resolve eq74 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq584
  have eq694 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 x X0
       have i₂ := eq592
       grind)
    | exact superpose eq592 eq24
    | exact resolve eq24 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq592
  have eq923 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (M.op X0 X0) X1
       have i₂ := eq87 X0 (M.op X0 X0)
       grind)
    | exact superpose eq87 eq102
    | (have j0 := eq102 (M.op X0 X0) X1
       grind)
    | exact resolve eq102 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq930 : ∀ X0 X1 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (k X1 (σ (τ (τ (M.op X0 X0))))) = (M.op X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (τ (τ (M.op X0 X0))) X1
       have i₂ := eq145 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq145 eq102
    | (have j0 := eq102 (τ (τ (M.op X0 X0))) X1
       grind)
    | exact resolve eq102 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq145
  have eq941 : ∀ X0 X1 : G, (k X1 (σ (τ (τ (M.op X0 X0))))) = (M.op X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq930 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq948 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq923 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq955 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq941 X0 X1
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq941
    | exact resolve eq941 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq961 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq948 X0 X1
       have i₂ := eq111 X1 X0
       grind)
    | exact superpose eq111 eq948
    | exact resolve eq948 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq948
  have eq968 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq112 X1 X0
       grind)
    | exact superpose eq112 eq955
    | exact resolve eq955 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq955
  have eq1021 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = X0 ∨ (M.op X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq968 (σ x) X0
       have i₂ := eq694 X1
       grind)
    | exact superpose eq694 eq968
    | (have j1 := eq694 X1
       grind)
    | exact resolve eq968 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq968
  have eq1063 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ (M.op X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1021 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1021
    | (have j0 := eq1021 X0 X0
       grind)
    | exact resolve eq1021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1816 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq1063 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1817 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq1816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1823 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq80 X0 x
       have i₂ := eq1817 x
       grind)
    | exact superpose eq1817 eq80
    | exact resolve eq80 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1838 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq961 x X0
       have i₂ := eq1817 x
       grind)
    | exact superpose eq1817 eq961
    | exact resolve eq961 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq1817
  have eq2407 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq80 X0 (σ x)
       have i₂ := eq1838 (σ x)
       grind)
    | exact superpose eq1838 eq80
    | exact resolve eq80 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1838
  have eq3916 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2407 (σ y)
       grind)
    | exact superpose eq2407 eq16
    | exact resolve eq16 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407
  have eq3974 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3916
       have i₂ := eq1823 y
       grind)
    | exact superpose eq1823 eq3916
    | exact resolve eq3916 eq1823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823 eq3916
  have eq3975 : False := by grind
  exact eq3975

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_y_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op X1 X0) X0
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq81 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq60 (M.op X1 X1) X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq350 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq512 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 (M.op X1 X1)
       have i₂ := eq86 X1 (σ X0)
       grind)
    | exact superpose eq86 eq350
    | exact resolve eq350 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq537 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq512
    | exact resolve eq512 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq664 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq665 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq664 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq3380 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq665 (M.op X0 X0)
       have i₂ := eq86 X0 (M.op X0 X0)
       grind)
    | exact superpose eq86 eq665
    | (have j0 := eq665 (M.op X0 X0)
       grind)
    | exact resolve eq665 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq3392 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq665 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq665
    | (have j0 := eq665 (τ X0)
       grind)
    | exact resolve eq665 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq665
  have eq3404 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3380
  have eq3409 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3392 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3392
    | (have j0 := eq3392 X0
       grind)
    | exact resolve eq3392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3419 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3409 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3409
    | (have j0 := eq3409 X0
       grind)
    | exact resolve eq3409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq19398 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ (M.op X0 X0)) X1
       have i₂ := eq3404 X0
       grind)
    | exact superpose eq3404 eq60
    | exact resolve eq60 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19399 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (σ (M.op X0 X0))
       have i₂ := eq3404 X0
       grind)
    | exact superpose eq3404 eq81
    | exact resolve eq81 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404
  have eq20045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq20046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq20045
    | exact resolve eq20045 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20045
  have eq20057 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq20046
       have r₂ := eq27
       grind)
    | exact resolve eq20046 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20046
  have eq20068 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20057 eq537
    | exact resolve eq537 eq20057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20057
  have eq20091 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq20068
    | exact resolve eq20068 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20068
  have eq20092 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq20091 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq20091 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq20091 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20091
  have eq20095 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq64 X0 x
       have i₂ := eq20092 (M.op x X0)
       grind)
    | exact superpose eq20092 eq64
    | (have j1 := eq20092 X0
       grind)
    | exact resolve eq64 eq20092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20106 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq20095 (M.op X1 X1)
       grind)
    | exact superpose eq20095 eq81
    | (have j1 := eq20095 X1
       grind)
    | exact resolve eq81 eq20095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20095
  have eq20757 : ∀ X0 : G, x = (M.op y x) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq20106
    | (have j0 := eq20106 (σ y) X0
       grind)
    | exact resolve eq20106 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20106
  have eq20800 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq64 x y
       have i₂ := eq20757 X0
       grind)
    | exact superpose eq20757 eq64
    | (have j1 := eq20757 X0
       grind)
    | exact resolve eq64 eq20757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20757
  have eq20827 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19399 x X1
       have i₂ := eq20800 X0
       grind)
    | exact superpose eq20800 eq19399
    | (have j1 := eq20800 X1
       grind)
    | exact resolve eq19399 eq20800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19399 eq20800
  have eq20839 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20827 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20827
    | (have j0 := eq20827 X0 X1
       grind)
    | exact resolve eq20827 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20827
  have eq23177 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq20839 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq20839 eq26
    | (have j1 := eq20839 (σ y) X0
       grind)
    | exact resolve eq26 eq20839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20839
  have eq23219 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq23177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23177
  have eq23282 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3419 y
       have i₂ := eq23219 y
       grind)
    | exact superpose eq23219 eq3419
    | (have j0 := eq3419 y
       grind)
    | (have r₁ := eq3419 y
       have r₂ := eq23219 y
       grind)
    | exact resolve eq3419 eq23219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23219
  have eq23315 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23282
  have eq23452 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19398 y X0
       have i₂ := eq23315
       grind)
    | exact superpose eq23315 eq19398
    | exact resolve eq19398 eq23315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19398 eq23315
  have eq23466 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23452 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23452
    | (have j0 := eq23452 X0
       grind)
    | exact resolve eq23452 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23452
  have eq24036 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23466 eq26
    | (have j1 := eq23466 (σ x)
       grind)
    | exact resolve eq26 eq23466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq23466
  have eq24037 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24036
  have eq24115 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq24037 eq27
    | exact resolve eq27 eq24037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq24116 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq24037 eq62
    | exact resolve eq62 eq24037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq24037
  have eq24122 : ∀ X0 : G, x = (M.op y x) ∨ (k X0 y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq24116
       have i₂ := eq20092 (M.op sF3 sF2)
       grind)
    | exact superpose eq20092 eq24116
    | (have j1 := eq20092 X0
       grind)
    | exact resolve eq24116 eq20092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20092
  have eq46882 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq64 x y
       have i₂ := eq24122 X0
       grind)
    | exact superpose eq24122 eq64
    | (have j1 := eq24122 X0
       grind)
    | exact resolve eq64 eq24122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq24122
  have eq47226 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (k X1 y) = X1 ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 x
       have i₂ := eq46882 X0
       grind)
    | exact superpose eq46882 eq81
    | (have j1 := eq46882 X1
       grind)
    | exact resolve eq81 eq46882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq46882
  have eq48724 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq47226 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47226
    | (have j0 := eq47226 y X0
       grind)
    | exact resolve eq47226 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47226
  have eq48865 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3419 y
       have i₂ := eq48724 y
       grind)
    | exact superpose eq48724 eq3419
    | (have j0 := eq3419 y
       grind)
    | (have r₁ := eq3419 y
       have r₂ := eq48724 y
       grind)
    | exact resolve eq3419 eq48724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48724
  have eq48940 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq48865
  have eq49537 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq48940
       grind)
    | exact superpose eq48940 eq60
    | exact resolve eq60 eq48940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq48940
  have eq50983 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq49537 x
       grind)
    | exact superpose eq49537 eq18
    | (have j1 := eq49537 x
       grind)
    | exact resolve eq18 eq49537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49537
  have eq50984 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq50983
  have eq50999 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50984 eq29
    | exact resolve eq29 eq50984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq50984
  have eq51181 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq50999
    | exact resolve eq50999 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50999
  have eq51521 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq51181 eq20
    | exact resolve eq20 eq51181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51181
  have eq51771 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq51521
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51521
    | exact resolve eq51521 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51521
  have eq51772 : x = y := by
    first
    | (have r₁ := eq51771
       have r₂ := eq24115
       grind)
    | exact resolve eq51771 eq24115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51771
  have eq51773 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq51772
       grind)
    | exact superpose eq51772 eq18
    | exact resolve eq18 eq51772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq51774 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq51772
       grind)
    | exact superpose eq51772 eq24
    | exact resolve eq24 eq51772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq51772
  have eq52029 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq51774
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51774
    | exact resolve eq51774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51774
  have eq52142 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq52029 eq24116
    | exact resolve eq24116 eq52029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24116 eq52029
  have eq52328 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq52142 eq537
    | exact resolve eq537 eq52142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq52142
  have eq52350 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq52328
    | exact resolve eq52328 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq52328
  have eq55750 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3419 x
       have i₂ := eq52350 x
       grind)
    | exact superpose eq52350 eq3419
    | (have j0 := eq3419 x
       grind)
    | (have r₁ := eq3419 x
       have r₂ := eq52350 x
       grind)
    | exact resolve eq3419 eq52350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419 eq52350
  have eq55832 : x = (M.op x x) := by grind
  clear eq55750
  have eq55915 : x = (M.op x y) := by
    first
    | (have i₁ := eq55832
       have i₂ := eq51773
       grind)
    | exact superpose eq51773 eq55832
    | exact resolve eq55832 eq51773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51773 eq55832
  have eq56268 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq55915 eq20
    | exact resolve eq20 eq55915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55915
  have eq56522 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56268
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56268
    | exact resolve eq56268 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq56268
  have eq56626 : False := by grind
  exact eq56626

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  clear eq24 eq35
  have eq50 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq51 X0 (M.op X0 X0)
       grind)
    | exact superpose eq51 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq51 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq68
    | exact resolve eq68 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq70 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 (M.op X0 (M.op X2 X2))) = (k (M.op X1 (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 (M.op X2 X2))) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 (M.op X2 X2))) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X0 (M.op X2 X2))) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (M.op X0 (M.op X2 X2))) = (k (M.op X1 (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq70 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 X1 X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq85
    | (have j0 := eq85 X0 X1 x
       grind)
    | exact resolve eq85 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq85
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq445 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq86
    | (have j0 := eq86 (σ y) (σ x)
       grind)
    | exact resolve eq86 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq112 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq710
    | exact resolve eq710 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq714 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq711
       have r₂ := eq27
       grind)
    | exact resolve eq711 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq726 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq714 eq50
    | exact resolve eq50 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq728 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq726
    | exact resolve eq726 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq731 : y ≠ y ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq728
       grind)
    | exact superpose eq728 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq728
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq728
       grind)
    | exact resolve eq12 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq733 : y = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq731
  have eq808 : ∀ X0 : G, x = (k x y) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq69 y X0
       have i₂ := eq733
       grind)
    | exact superpose eq733 eq69
    | exact resolve eq69 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq991 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq808 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq992 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq991
  have eq995 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq44
    | exact resolve eq44 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq992
  have eq997 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq995
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq995
    | exact resolve eq995 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1061 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq997 eq92
    | (have j0 := eq92 (σ y) (σ x)
       grind)
    | exact resolve eq92 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq997
  have eq1062 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1061
    | exact resolve eq1061 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1063 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1062
  have eq1070 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1063 eq50
    | exact resolve eq50 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1072 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1070
    | exact resolve eq1070 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1070
  have eq1073 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1072
  have eq1075 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1073 eq27
    | exact resolve eq27 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1079 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1073 eq445
    | exact resolve eq445 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq1073
  have eq1214 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1079 eq69
    | exact resolve eq69 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1079
  have eq1379 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have j0 := eq1214 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1380 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1379
  have eq1386 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1380 eq112
    | exact resolve eq112 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq1380
  have eq1390 : y = (M.op y x) := by
    first
    | (have r₁ := eq1386
       have r₂ := eq1075
       grind)
    | exact resolve eq1386 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1458 : x = (M.op x y) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq1390
       grind)
    | exact superpose eq1390 eq50
    | exact resolve eq50 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1390
  have eq1460 : x = (M.op x y) := by
    first
    | (have i₁ := eq1458
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1458
    | exact resolve eq1458 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1458
  have eq1461 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1460 eq20
    | exact resolve eq20 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1460
  have eq1488 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1461
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1461
    | exact resolve eq1461 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1461
  have eq1490 : False := by grind
  exact eq1490

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq112 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq9122
    | exact resolve eq9122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9122
  have eq9134 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq9123
       have r₂ := eq28
       grind)
    | exact resolve eq9123 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9123
  have eq9138 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq9134
    | exact resolve eq9134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9134
  have eq9140 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9138 eq79
    | (have r₁ := eq79
       have r₂ := eq9138
       grind)
    | exact resolve eq79 eq9138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq9138
  have eq9170 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq9140
  have eq9171 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq9170
  have eq9481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9171 eq92
    | exact resolve eq92 eq9171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq9171
  have eq9491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9481
  have eq9494 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9491
       have r₂ := eq28
       grind)
    | exact resolve eq9491 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9491
  have eq9496 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq9494
       grind)
    | exact superpose eq9494 eq52
    | exact resolve eq52 eq9494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq9497 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq9494
       grind)
    | exact superpose eq9494 eq77
    | (have r₁ := eq77
       have r₂ := eq9494
       grind)
    | exact resolve eq77 eq9494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq9494
  have eq9524 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq9497
  have eq9525 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9524
  have eq9538 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq9496
    | exact resolve eq9496 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9496
  have eq9896 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq9525
       grind)
    | exact superpose eq9525 eq49
    | exact resolve eq49 eq9525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq9525
  have eq9914 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq9896
    | exact resolve eq9896 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9896
  have eq10546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9914 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914
  have eq10547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10546
  have eq10551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq10547
    | exact resolve eq10547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10547
  have eq10562 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10551
       have r₂ := eq28
       grind)
    | exact resolve eq10551 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10551
  have eq10566 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq10562
    | exact resolve eq10562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10562
  have eq10604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10566 eq9538
    | exact resolve eq9538 eq10566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9538 eq10566
  have eq10625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10604
  have eq10629 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10625
       have r₂ := eq28
       grind)
    | exact resolve eq10625 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10625
  have eq10632 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq10629 eq30
    | exact resolve eq30 eq10629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10629
  have eq10745 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq10632
    | exact resolve eq10632 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10632
  have eq10746 : x = y := by grind
  clear eq10745
  have eq10893 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq10746
       grind)
    | exact superpose eq10746 eq19
    | exact resolve eq19 eq10746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq10894 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq10746
       grind)
    | exact superpose eq10746 eq25
    | exact resolve eq25 eq10746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq10746
  have eq10995 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10894
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10894
    | exact resolve eq10894 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10894
  have eq11010 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10995 eq27
    | exact resolve eq27 eq10995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10995
  have eq11230 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11010 eq112
    | exact resolve eq112 eq11010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq11010
  have eq11268 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11230
       have i₂ := eq10893
       grind)
    | exact superpose eq10893 eq11230
    | exact resolve eq11230 eq10893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10893 eq11230
  have eq11593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11268 eq15
    | exact resolve eq15 eq11268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11268
  have eq11635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11593
    | exact resolve eq11593 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq11593
  have eq11642 : False := by grind
  exact eq11642

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq110 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq110 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq110
    | exact resolve eq110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq708 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq715 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq708
    | (have j0 := eq708 X0 X1
       grind)
    | exact resolve eq708 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq3102 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq715 x y
       grind)
    | exact superpose eq715 eq16
    | (have j1 := eq715 x y
       grind)
    | exact resolve eq16 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq21045 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq707
    | exact resolve eq707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq21150 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21045 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq21045
    | (have j0 := eq21045 X0 X1
       grind)
    | exact resolve eq21045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21045
  have eq33188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3102
       have i₂ := eq21150 y x
       grind)
    | exact superpose eq21150 eq3102
    | (have j1 := eq21150 y x
       grind)
    | (have r₁ := eq3102
       have r₂ := eq21150 y x
       grind)
    | (have r₁ := eq3102
       have r₂ := eq21150 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3102
       have r₂ := eq21150 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3102 eq21150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102 eq21150
  have eq33189 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq33188
  have eq122584 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33189
       grind)
    | exact superpose eq33189 eq16
    | exact resolve eq16 eq33189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33189
  have eq122585 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq122584
       have r₂ := eq23 x
       grind)
    | exact resolve eq122584 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122584
  have eq122589 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq122585
       grind)
    | exact superpose eq122585 eq10
    | exact resolve eq10 eq122585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122585
  have eq122707 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq122589
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq122589
    | exact resolve eq122589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122589
  have eq122709 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq122707
       grind)
    | exact superpose eq122707 eq16
    | exact resolve eq16 eq122707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122707
  have eq122714 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq122709
       have r₂ := eq23 x
       grind)
    | exact resolve eq122709 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq122709
  have eq122804 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq122714
       grind)
    | exact superpose eq122714 eq10
    | exact resolve eq10 eq122714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122714
  have eq122929 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq122804
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq122804
    | exact resolve eq122804 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122804
  have eq122930 : y = (M.op x x) := by grind
  clear eq122929
  have eq122941 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq110 x X0
       have i₂ := eq122930
       grind)
    | exact superpose eq122930 eq110
    | exact resolve eq110 eq122930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq122944 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq118 x X0
       have i₂ := eq122930
       grind)
    | exact superpose eq122930 eq118
    | exact resolve eq118 eq122930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq122930
  have eq124754 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq122944 (σ x)
       grind)
    | exact superpose eq122944 eq16
    | exact resolve eq16 eq122944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122944
  have eq124764 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq124754
       have i₂ := eq122941 x
       grind)
    | exact superpose eq122941 eq124754
    | exact resolve eq124754 eq122941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122941 eq124754
  have eq124765 : False := by grind
  exact eq124765

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_x_pxx_pyx_Equation4400 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4400 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) x x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op X0 (M.op X0 X1))
       have r₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 X0 X1 X3
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq189 : ∀ X1 : G, (M.op (M.op x (M.op x y)) X1) = (M.op (M.op x y) (M.op x (M.op x y))) := by
    intro X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X1) := by
    intro X1
    first
    | exact superpose eq180 eq189
    | exact resolve eq189 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq193 : (M.op x (M.op x y)) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq191 x
       have i₂ := eq16 x sF0 x
       grind)
    | exact superpose eq16 eq191
    | exact resolve eq191 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq490 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq498 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) ∨ x = (M.op x (M.op x (M.op x y))) ∨ x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq193
       have i₂ := eq11 (M.op x sF0) x
       grind)
    | exact superpose eq11 eq193
    | (have j1 := eq11 (M.op x (M.op x y)) x
       grind)
    | exact resolve eq193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq531 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) ∨ x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have j1 := eq184 x (M.op x y) x
       grind)
    | (have r₁ := eq513
       have r₂ := eq184 x y (k (M.op x (M.op x y)) x)
       grind)
    | (have r₁ := eq513
       have r₂ := eq184 x (M.op x y) x
       grind)
    | exact resolve eq513 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq513
  have eq562 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) := by
    first
    | (have j1 := eq13 (M.op x (M.op x y)) x
       grind)
    | (have r₁ := eq546
       have r₂ := eq13 (M.op x (M.op x y)) x
       grind)
    | exact resolve eq546 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq609 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | exact superpose eq180 eq562
    | exact resolve eq562 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq616 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (k (σ (M.op (M.op x y) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq609 eq39
    | exact resolve eq39 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq979 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) x
       have i₂ := eq185 X0 X1 x
       grind)
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq490
       grind)
    | exact superpose eq490 eq39
    | exact resolve eq39 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1014 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1013
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1013
    | exact resolve eq1013 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1016 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1014
    | exact resolve eq1014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1170 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq979 X0 X1
       grind)
    | exact superpose eq979 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq979 X0 X1
       grind)
    | exact resolve eq13 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1199 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1256 : ∀ X0 : G, (σ y) = (k (σ y) (σ (M.op y (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op y (M.op y X0))
       have i₂ := eq1199 y X0
       grind)
    | exact superpose eq1199 eq36
    | exact resolve eq36 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1260 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq107 (M.op sF3 (M.op sF3 x))
       have i₂ := eq1199 sF3 x
       grind)
    | exact superpose eq1199 eq107
    | exact resolve eq107 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1199
  have eq1261 : ∀ X0 : G, y = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq31 eq1260
    | exact resolve eq1260 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1260
  have eq1265 : ∀ X0 : G, (σ y) = (k (σ y) (σ (M.op y (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq1256 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1256
    | (have j0 := eq1256 X0
       grind)
    | exact resolve eq1256 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq2162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1016 eq498
    | exact resolve eq498 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq1016
  have eq2171 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2162
       have r₂ := eq27
       grind)
    | exact resolve eq2162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq2176 : y = (k y (τ (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2171 eq1261
    | exact resolve eq1261 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq2201 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2171 eq2176
    | exact resolve eq2176 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2206 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq2201
    | exact resolve eq2201 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2209 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq2206
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2206 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2212 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq490
       have i₂ := eq2209
       grind)
    | exact superpose eq2209 eq490
    | exact resolve eq490 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq2209
  have eq2216 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2212
  have eq2247 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y x x
       have i₂ := eq2216
       grind)
    | exact superpose eq2216 eq16
    | exact resolve eq16 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2265 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2216 eq2247
    | exact resolve eq2247 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216 eq2247
  have eq2372 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2265 y
       grind)
    | exact superpose eq2265 eq18
    | (have j1 := eq2265 y
       grind)
    | exact resolve eq18 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq2399 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2372
  have eq2411 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2399 eq181
    | exact resolve eq181 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2430 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2411 eq26
    | (have j1 := eq2411 (σ y)
       grind)
    | exact resolve eq26 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq2475 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2399 eq2430
    | exact resolve eq2430 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2481 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2475 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2475
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2475
       grind)
    | exact resolve eq13 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475
  have eq2492 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2481
  have eq2504 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2492 eq141
    | exact resolve eq141 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492
  have eq2510 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2504
    | exact resolve eq2504 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq2564 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq531 x x
       have i₂ := eq2510
       grind)
    | exact superpose eq2510 eq531
    | (have j0 := eq531 x x
       grind)
    | (have r₁ := eq531 x x
       have r₂ := eq2510
       grind)
    | exact resolve eq531 eq2510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2565 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2564
  have eq2566 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2565
  have eq2574 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x x x x
       have i₂ := eq2566
       grind)
    | exact superpose eq2566 eq176
    | exact resolve eq176 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2873 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2566
       have i₂ := eq2574 x X0
       grind)
    | (have i₁ := eq2566
       have i₂ := eq2574 X0 x
       grind)
    | exact superpose eq2574 eq2566
    | exact resolve eq2566 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566
  have eq2874 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq2574 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq2574 X0 y
       grind)
    | exact superpose eq2574 eq18
    | (have j1 := eq2574 y X0
       grind)
    | exact resolve eq18 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2902 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq2915 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2874 eq2902
    | (have j0 := eq2902 y
       grind)
    | exact resolve eq2902 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874 eq2902
  have eq2916 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2915
  have eq2926 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2916
       grind)
    | exact superpose eq2916 eq18
    | exact resolve eq18 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2927 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2916
       grind)
    | exact superpose eq2916 eq24
    | exact resolve eq24 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2933 : ∀ X0 : G, (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op (M.op x y) X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1265 X0
       have i₂ := eq2916
       grind)
    | exact superpose eq2916 eq1265
    | exact resolve eq1265 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq2916
  have eq2944 : (σ y) = (k (σ y) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq180 eq2933
    | exact resolve eq2933 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq2948 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2927
    | exact resolve eq2927 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq2949 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2926 eq2944
    | exact resolve eq2944 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944
  have eq2950 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2949
    | exact resolve eq2949 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2949
  have eq2951 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2948 eq2950
    | exact resolve eq2950 eq2948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2948 eq2950
  have eq2987 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2926 eq180
    | exact resolve eq180 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq3057 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2951 eq531
    | (have j0 := eq531 (σ y) (σ y)
       grind)
    | (have r₁ := eq531 (σ y) (σ y)
       have r₂ := eq2951
       grind)
    | exact resolve eq531 eq2951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951
  have eq3058 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3057
  have eq3059 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3058
  have eq3158 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3059 eq176
    | exact resolve eq176 eq3059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3059
  have eq3219 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3158 eq2171
    | exact resolve eq2171 eq3158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq3158
  have eq3240 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq3219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219
  have eq3256 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq2399 eq3240
    | (have j0 := eq3240 X0
       grind)
    | exact resolve eq3240 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399 eq3240
  have eq3263 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2987 eq3256
    | (have j0 := eq3256 X0
       grind)
    | exact resolve eq3256 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2987 eq3256
  have eq3264 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq3699 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq3264 eq185
    | exact resolve eq185 eq3264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq3264
  have eq3749 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3699 eq26
    | (have j1 := eq3699 (σ y)
       grind)
    | exact resolve eq26 eq3699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq3777 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3749
  have eq3802 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3777 eq181
    | exact resolve eq181 eq3777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq3841 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3802 eq26
    | (have j1 := eq3802 (σ y)
       grind)
    | exact resolve eq26 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802
  have eq3922 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3777 eq3841
    | exact resolve eq3841 eq3777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777 eq3841
  have eq3936 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3922 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq3922
       grind)
    | exact resolve eq13 eq3922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq3949 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3936
  have eq3967 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3949 eq141
    | exact resolve eq141 eq3949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3949
  have eq3976 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3967
    | exact resolve eq3967 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3967
  have eq4055 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq531 x x
       have i₂ := eq3976
       grind)
    | exact superpose eq3976 eq531
    | (have j0 := eq531 x x
       grind)
    | (have r₁ := eq531 x x
       have r₂ := eq3976
       grind)
    | exact resolve eq531 eq3976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq4056 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq4055
  have eq4057 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq4056
  have eq4073 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x x x x
       have i₂ := eq4057
       grind)
    | exact superpose eq4057 eq176
    | exact resolve eq176 eq4057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4446 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4057
       have i₂ := eq4073 x X0
       grind)
    | (have i₁ := eq4057
       have i₂ := eq4073 X0 x
       grind)
    | exact superpose eq4073 eq4057
    | exact resolve eq4057 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057
  have eq4458 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2926
       have i₂ := eq4073 sF0 x
       grind)
    | (have i₁ := eq2926
       have i₂ := eq4073 X0 sF0
       grind)
    | exact superpose eq4073 eq2926
    | (have j1 := eq4073 y X0
       grind)
    | exact resolve eq2926 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926 eq4073
  have eq4479 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4458 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4458
  have eq4481 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446
  have eq4518 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4479 eq4481
    | (have j0 := eq4481 y
       grind)
    | exact resolve eq4481 eq4479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479 eq4481
  have eq4519 : x = (M.op x y) := by grind
  clear eq4518
  have eq4546 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4519
       grind)
    | exact superpose eq4519 eq18
    | exact resolve eq18 eq4519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4547 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4519
       grind)
    | exact superpose eq4519 eq22
    | exact resolve eq22 eq4519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4519
  have eq4572 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4547 eq20
    | exact resolve eq20 eq4547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4547
  have eq4660 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq4546 eq616
    | exact resolve eq616 eq4546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq4546
  have eq4683 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq4660
    | exact resolve eq4660 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4660
  have eq4691 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4572 eq4683
    | exact resolve eq4683 eq4572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4683
  have eq4773 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4691 eq531
    | (have j0 := eq531 (σ x) (σ x)
       grind)
    | (have r₁ := eq531 (σ x) (σ x)
       have r₂ := eq4691
       grind)
    | exact resolve eq531 eq4691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq4691
  have eq4774 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4773
  have eq4775 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4774
  have eq4806 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | exact superpose eq4775 eq176
    | exact resolve eq176 eq4775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq4937 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq4806 eq4775
    | exact resolve eq4775 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775 eq4806
  have eq5011 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4937 eq26
    | (have j1 := eq4937 (σ y)
       grind)
    | exact resolve eq26 eq4937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4937
  have eq5407 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5011 eq27
    | exact resolve eq27 eq5011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5011
  have eq5423 : False := by grind
  exact eq5423

/-- `Equation4404`: `x ◇ (x ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_x_pxy_pyx_Equation4404 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4404 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4404.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
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
  have eq176 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X4) X5) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X4 X5
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X0 X2) X4) X5) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X2) x X4 X5
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X0 x X4 X5
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X0 X2 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X4 X1 (M.op (M.op X0 X1) x)
       have i₂ := eq16 (M.op X0 X1) x X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ X3 ∨ (M.op X0 X2) = (k (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X2) X3
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 X2) X3
       grind)
    | (have r₁ := eq13 (M.op X0 X2) (M.op X0 (M.op X0 X1))
       have r₂ := eq16 X0 X1 X2 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X2 X3 : G, (M.op (M.op x y) X0) = (M.op (M.op x X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq182 x X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq209 : ∀ X0 : G, (M.op x (M.op x y)) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq188 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x (M.op x y))
       have r₂ := eq188 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq183
    | (have j0 := eq183 (σ y) X0
       grind)
    | exact resolve eq183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X2
    first
    | exact superpose eq183 eq183
    | exact resolve eq183 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X2
    first
    | exact superpose eq183 eq183
    | exact resolve eq183 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X2) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq367 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq195 eq188
    | exact resolve eq188 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq244 eq237
    | exact resolve eq237 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq687 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq699 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 x
       have i₂ := eq11 (M.op sF4 X0) sF2
       grind)
    | exact superpose eq11 eq238
    | (have j1 := eq11 (M.op (M.op (σ x) (σ y)) X0) (σ x)
       grind)
    | exact resolve eq238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq756 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq237 eq745
    | (have j0 := eq745 X0 X1
       grind)
    | exact resolve eq745 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq813 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq237 eq770
    | (have j0 := eq770 X0 x
       grind)
    | exact resolve eq770 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq838 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq237 eq813
    | (have j0 := eq813 X0
       grind)
    | exact resolve eq813 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq841 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq838 X0
       have j1 := eq187 (σ x) x (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq838 X0
       have r₂ := eq187 (σ x) (M.op (σ x) (σ y)) x (σ x)
       grind)
    | (have r₁ := eq838 X0
       have r₂ := eq187 (σ x) (σ y) x (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x))
       grind)
    | exact resolve eq838 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq838
  have eq843 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq237 eq841
    | exact resolve eq841 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq841
  have eq844 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have j1 := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (σ x)
       grind)
    | (have r₁ := eq843
       have r₂ := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (σ x)
       grind)
    | exact resolve eq843 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1000 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (τ (M.op (σ x) (M.op (σ x) (σ y)))) x) := by
    first
    | exact superpose eq844 eq141
    | exact resolve eq141 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq844
  have eq1233 : (M.op x y) = (k (M.op x y) (M.op x (M.op x y))) := by
    first
    | (have j0 := eq209 (M.op x (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq1234 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq188 eq1233
    | exact resolve eq1233 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1247 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq1234 eq37
    | exact resolve eq37 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1234
  have eq1248 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq20 eq1247
    | (have j0 := eq1247 X0
       grind)
    | exact resolve eq1247 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq2658 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X0 X3) X4) ∨ (k X0 (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X3) X4)
       have i₂ := eq176 X0 X3 X4 X1 X2
       grind)
    | exact superpose eq176 eq13
    | (have j0 := eq13 X0 (M.op (M.op X0 X3) X4)
       grind)
    | (have r₁ := eq13 (M.op X0 X4) (M.op X0 (M.op (M.op X0 X1) X2))
       have r₂ := eq176 X0 X1 X2 X4 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X4) x)
       have r₂ := eq176 X0 X4 x X4 x
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2776 : ∀ X0 X3 X4 : G, (k X0 (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X3 X4
    first
    | (have j0 := eq2658 X0 x x X3 X4
       grind)
    | (have r₁ := eq2658 X0 x x X4 x
       have r₂ := eq178 X0 x x X4 x
       grind)
    | (have r₁ := eq2658 X0 X4 x x x
       have r₂ := eq178 X0 x x X4 x
       grind)
    | exact resolve eq2658 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq2658
  have eq3378 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2776 X0 x x
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq2776
    | exact resolve eq2776 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3389 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op (M.op y X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op (M.op y X0) X1)
       have i₂ := eq2776 y X0 X1
       grind)
    | exact superpose eq2776 eq36
    | exact resolve eq36 eq2776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2776
  have eq3398 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op (M.op y X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3389 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3389
    | (have j0 := eq3389 X0 X1
       grind)
    | exact resolve eq3389 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389
  have eq3538 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq107 (M.op sF3 (M.op sF3 x))
       have i₂ := eq3378 sF3 x
       grind)
    | exact superpose eq3378 eq107
    | exact resolve eq107 eq3378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq3378
  have eq3539 : ∀ X0 : G, y = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq31 eq3538
    | exact resolve eq3538 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3538
  have eq3587 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op y (M.op (M.op y X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3398 x x
       have i₂ := eq176 y X0 X1 x x
       grind)
    | exact superpose eq176 eq3398
    | exact resolve eq3398 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq3398
  have eq5123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq39
    | exact resolve eq39 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq5124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq5123
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5123
    | exact resolve eq5123 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5123
  have eq5126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq5124
    | exact resolve eq5124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5124
  have eq7641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5126 eq699
    | exact resolve eq699 eq5126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq5126
  have eq7650 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq7641
       have r₂ := eq27
       grind)
    | exact resolve eq7641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7641
  have eq7657 : y = (k y (τ (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7650 eq3539
    | exact resolve eq3539 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539
  have eq7686 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7650 eq7657
    | exact resolve eq7657 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7657
  have eq7690 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq7686
    | exact resolve eq7686 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7686
  have eq7692 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq7690
       have r₂ := eq13 y x
       grind)
    | exact resolve eq7690 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7690
  have eq7694 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq687
       have i₂ := eq7692
       grind)
    | exact superpose eq7692 eq687
    | exact resolve eq687 eq7692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq7692
  have eq7698 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7694
  have eq7738 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq184 y X0 x
       have i₂ := eq7698
       grind)
    | exact superpose eq7698 eq184
    | exact resolve eq184 eq7698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7752 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7698 eq7738
    | exact resolve eq7738 eq7698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7698 eq7738
  have eq7956 : ∀ X1 X2 X3 : G, x = (M.op (M.op (M.op y X1) X2) X3) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq185 y X1 X2 X3 x
       have i₂ := eq7752 x
       grind)
    | exact superpose eq7752 eq185
    | exact resolve eq185 eq7752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq7959 : ∀ X1 X2 : G, x = (M.op (M.op y X1) X2) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq16 y x X1 X2
       have i₂ := eq7752 x
       grind)
    | exact superpose eq7752 eq16
    | exact resolve eq16 eq7752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7752
  have eq7993 : ∀ X3 : G, x = (M.op x X3) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X3
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f7993_14 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op y X0) X1) X2) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      grind
    have f7993_15 : ∀ X0 X1 : G, x = (M.op (M.op y X0) X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f7993_24 : x ≠ (M.op x y) := by grind
    have f7993_25 : y ≠ (M.op x y) := by grind
    have f7993_26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f7993_27 : ∀ X0 X1 : G, x = (M.op (M.op y X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f7993_15 X0 X1
         grind)
      | (have r₁ := f7993_15 X0 X1
         have r₂ := f7993_24
         grind)
      | exact resolve f7993_15 f7993_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7993_28 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op y X0) X1) X2) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      first
      | (have j0 := f7993_14 X0 X1 X2
         grind)
      | (have r₁ := f7993_14 X0 X1 X2
         have r₂ := f7993_24
         grind)
      | exact resolve f7993_14 f7993_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7993_29 : ∀ X0 X1 : G, x = (M.op (M.op y X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f7993_27 X0 X1
         grind)
      | (have r₁ := f7993_27 X0 X1
         have r₂ := f7993_25
         grind)
      | exact resolve f7993_27 f7993_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7993_30 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op y X0) X1) X2) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      first
      | (have j0 := f7993_28 X0 X1 X2
         grind)
      | (have r₁ := f7993_28 X0 X1 X2
         have r₂ := f7993_25
         grind)
      | exact resolve f7993_28 f7993_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7993_31 : ∀ X0 X1 : G, x = (M.op (M.op y X0) X1) := by
      intro X0 X1
      first
      | (have j0 := f7993_29 X0 X1
         grind)
      | (have r₁ := f7993_29 X0 X1
         have r₂ := f7993_26
         grind)
      | exact resolve f7993_29 f7993_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7993_32 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op y X0) X1) X2) := by
      intro X0 X1 X2
      first
      | (have j0 := f7993_30 X0 X1 X2
         grind)
      | (have r₁ := f7993_30 X0 X1 X2
         have r₂ := f7993_26
         grind)
      | exact resolve f7993_30 f7993_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7993_33 : ∀ X2 : G, x = (M.op x X2) := by
      intro X2
      first
      | (have i₁ := f7993_32 x x X2
         have i₂ := f7993_31 x x
         grind)
      | exact superpose f7993_31 f7993_32
      | exact resolve f7993_32 f7993_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7993_36 : x ≠ x := by
      first
      | (have i₁ := f7993_24
         have i₂ := f7993_33 y
         grind)
      | exact superpose f7993_33 f7993_24
      | (have r₁ := f7993_24
         have r₂ := f7993_33 y
         grind)
      | exact resolve f7993_24 f7993_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7993_37 : False := by grind
    exact f7993_37
  clear eq7956 eq7959
  have eq8053 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7993 y
       grind)
    | exact superpose eq7993 eq18
    | (have j1 := eq7993 y
       grind)
    | exact resolve eq18 eq7993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7993
  have eq8094 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8053
  have eq8122 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8094 eq240
    | exact resolve eq240 eq8094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8259 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8122 eq26
    | (have j1 := eq8122 (σ y) X0
       grind)
    | exact resolve eq26 eq8122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8310 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8094 eq8259
    | exact resolve eq8259 eq8094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8259
  have eq8407 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8310 eq1000
    | exact resolve eq1000 eq8310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8310
  have eq8455 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8407
    | exact resolve eq8407 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8407
  have eq8503 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq756 x x
       have i₂ := eq8455
       grind)
    | exact superpose eq8455 eq756
    | (have j0 := eq756 x x
       grind)
    | (have r₁ := eq756 x x
       have r₂ := eq8455
       grind)
    | exact resolve eq756 eq8455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8455
  have eq8504 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8503
  have eq8505 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8504
  have eq8512 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op x X1) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 x X1
       have i₂ := eq8505
       grind)
    | exact superpose eq8505 eq195
    | exact resolve eq195 eq8505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq8728 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8505
       have i₂ := eq8512 X0 x
       grind)
    | exact superpose eq8512 eq8505
    | exact resolve eq8505 eq8512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq8729 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq8512 X0 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq8512 X0 x
       grind)
    | exact superpose eq8512 eq18
    | (have j1 := eq8512 X0 y
       grind)
    | exact resolve eq18 eq8512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8512
  have eq8770 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8728 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8728
  have eq8791 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8729 eq8770
    | exact resolve eq8770 eq8729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8729 eq8770
  have eq8792 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8791
  have eq8830 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8792
       grind)
    | exact superpose eq8792 eq18
    | exact resolve eq18 eq8792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8831 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8792
       grind)
    | exact superpose eq8792 eq24
    | exact resolve eq24 eq8792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8840 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3587 X0 X1
       have i₂ := eq8792
       grind)
    | exact superpose eq8792 eq3587
    | exact resolve eq3587 eq8792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587 eq8792
  have eq8857 : (σ y) = (k (σ y) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq188 eq8840
    | exact resolve eq8840 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq8840
  have eq8863 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8831
    | exact resolve eq8831 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8831
  have eq8865 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8830 eq8857
    | exact resolve eq8857 eq8830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8857
  have eq8869 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8865
    | exact resolve eq8865 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8865
  have eq8873 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8863 eq8869
    | exact resolve eq8869 eq8863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8863 eq8869
  have eq8939 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8830 eq367
    | exact resolve eq367 eq8830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9462 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8873 eq756
    | (have j0 := eq756 (σ y) (σ y)
       grind)
    | (have r₁ := eq756 (σ y) (σ y)
       have r₂ := eq8873
       grind)
    | exact resolve eq756 eq8873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8873
  have eq9463 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9462
  have eq9464 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9463
  have eq9653 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9464 eq184
    | exact resolve eq184 eq9464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9668 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9464 eq9653
    | exact resolve eq9653 eq9464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9464 eq9653
  have eq9797 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq7650 eq177
    | exact resolve eq177 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq10151 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X2
    first
    | exact superpose eq441 eq9797
    | exact resolve eq9797 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9797
  have eq10164 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X2
    first
    | exact superpose eq8122 eq10151
    | (have j0 := eq10151 X2
       have j1 := eq8122 (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) X2))
       grind)
    | exact resolve eq10151 eq8122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8122 eq10151
  have eq10171 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq8939 eq10164
    | (have j0 := eq10164 X2
       grind)
    | exact resolve eq10164 eq8939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10164
  have eq10172 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | (have j0 := eq10171 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10171
  have eq10174 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9668 eq10172
    | exact resolve eq10172 eq9668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10172
  have eq10175 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10174
    | exact resolve eq10174 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10174
  have eq10218 : ∀ X1 X2 : G, (σ y) = (M.op (M.op (σ y) X1) X2) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq9668 eq16
    | exact resolve eq16 eq9668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10268 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq7650 eq10218
    | exact resolve eq10218 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10270 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq9668 eq10218
    | exact resolve eq10218 eq9668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9668 eq10218
  have eq10348 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq10270 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10270
  have eq10350 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq10268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10268
  have eq10361 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq8094 eq10350
    | (have j0 := eq10350 X0
       grind)
    | exact resolve eq10350 eq8094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10350
  have eq10364 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8939 eq10361
    | (have j0 := eq10361 X0
       grind)
    | exact resolve eq10361 eq8939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10361
  have eq10365 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10364
  have eq10386 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10348 eq7650
    | exact resolve eq7650 eq10348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7650 eq10348
  have eq10424 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq10386
  have eq10432 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq8094 eq10424
    | exact resolve eq10424 eq8094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8094 eq10424
  have eq10438 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8939 eq10432
    | exact resolve eq10432 eq8939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8939 eq10432
  have eq10439 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq10438
  have eq10908 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10365 eq10175
    | (have j1 := eq10365 (σ y)
       grind)
    | exact resolve eq10175 eq10365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10175 eq10365
  have eq10946 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10908
  have eq10982 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10439 eq10946
    | exact resolve eq10946 eq10439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10439 eq10946
  have eq10983 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10982
  have eq11048 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq10983 eq240
    | exact resolve eq240 eq10983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq11981 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11048 eq26
    | (have j1 := eq11048 (σ y) X0
       grind)
    | exact resolve eq26 eq11048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11048
  have eq12067 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10983 eq11981
    | exact resolve eq11981 eq10983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10983 eq11981
  have eq12173 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12067 eq1000
    | exact resolve eq1000 eq12067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq12067
  have eq12244 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq12173
    | exact resolve eq12173 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12173
  have eq12296 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq756 x x
       have i₂ := eq12244
       grind)
    | exact superpose eq12244 eq756
    | (have j0 := eq756 x x
       grind)
    | (have r₁ := eq756 x x
       have r₂ := eq12244
       grind)
    | exact resolve eq756 eq12244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12244
  have eq12297 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12296
  have eq12298 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12297
  have eq12314 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq367 x X0
       have i₂ := eq12298
       grind)
    | exact superpose eq12298 eq367
    | exact resolve eq367 eq12298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq12359 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8830 eq12314
    | exact resolve eq12314 eq8830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8830 eq12314
  have eq12423 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12298
       have i₂ := eq12359 x
       grind)
    | exact superpose eq12359 eq12298
    | exact resolve eq12298 eq12359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12298 eq12359
  have eq12477 : x = (M.op x y) := by grind
  clear eq12423
  have eq12497 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12477
       grind)
    | exact superpose eq12477 eq18
    | exact resolve eq18 eq12477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12498 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq12477
       grind)
    | exact superpose eq12477 eq22
    | exact resolve eq22 eq12477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12477
  have eq12540 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12498 eq20
    | exact resolve eq20 eq12498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12498
  have eq12645 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12497 eq1248
    | exact resolve eq1248 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq12497
  have eq12684 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq12645
    | exact resolve eq12645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12645
  have eq12689 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq12540 eq12684
    | exact resolve eq12684 eq12540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12684
  have eq12867 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12689 eq756
    | (have j0 := eq756 (σ x) (σ x)
       grind)
    | (have r₁ := eq756 (σ x) (σ x)
       have r₂ := eq12689
       grind)
    | exact resolve eq756 eq12689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq12689
  have eq12868 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12867
  have eq12869 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12868
  have eq12895 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq12869 eq441
    | exact resolve eq441 eq12869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12915 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq12869 eq184
    | exact resolve eq184 eq12869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq12931 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq12869 eq12915
    | exact resolve eq12915 eq12869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12869 eq12915
  have eq12936 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12895 eq12931
    | (have j0 := eq12931 (σ y)
       grind)
    | exact resolve eq12931 eq12895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12895 eq12931
  have eq12967 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq12936 eq441
    | exact resolve eq441 eq12936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq12936
  have eq13086 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12967 eq26
    | (have j1 := eq12967 (σ y)
       grind)
    | exact resolve eq26 eq12967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12967
  have eq13180 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq13086 eq27
    | exact resolve eq27 eq13086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13086
  have eq13217 : False := by grind
  exact eq13217
