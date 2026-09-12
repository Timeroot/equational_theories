import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
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
  have eq64 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
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
  have eq68 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq68 (τ X0) X1
       grind)
    | exact superpose eq68 eq17
    | exact resolve eq17 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq81 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq81 (τ X0) X1
       grind)
    | exact superpose eq81 eq17
    | exact resolve eq17 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq89 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq132 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq71
    | (have j0 := eq71 X2 X2
       grind)
    | exact resolve eq71 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq235 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq89 (τ X0) X1
       grind)
    | exact superpose eq89 eq17
    | exact resolve eq17 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq237 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq235
    | exact resolve eq235 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq305 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq237 (τ X0) X1
       grind)
    | exact superpose eq237 eq17
    | exact resolve eq17 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq309 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq305
    | exact resolve eq305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq388 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))
       have i₂ := eq309 (τ X0) X1
       grind)
    | exact superpose eq309 eq17
    | exact resolve eq17 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq392 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq388
    | exact resolve eq388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq2394 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X0) (k X1 (σ X2))
       have i₂ := eq132 X1 X2 X0
       grind)
    | exact superpose eq132 eq19
    | (have j1 := eq132 X1 X2 X0
       grind)
    | exact resolve eq19 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq132
  have eq2395 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2394 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq17343 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2395 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2395
    | exact resolve eq2395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq17437 : ∀ X0 X1 X2 : G, (k (σ (k (τ X1) X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17343 X0 X1 X2
       have i₂ := eq18 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq18 eq17343
    | (have j0 := eq17343 X0 X1 X2
       grind)
    | exact resolve eq17343 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17343
  have eq17452 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17437 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq17437
    | (have j0 := eq17437 X0 X1 X2
       grind)
    | exact resolve eq17437 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq17437
  have eq17453 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17452 X0 X1 X2
       have j1 := eq12 (k X1 (σ X2)) X0
       grind)
    | (have r₁ := eq17452 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq17452 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17452
  have eq17483 : ∀ X0 X2 : G, (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq17453 X0 X0 (σ (σ (σ (σ (σ (M.op x x))))))
       have i₂ := eq392 X0 x
       grind)
    | exact superpose eq392 eq17453
    | exact resolve eq17453 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq17453
  have eq17994 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq17483 (σ X0) (σ X1)
       grind)
    | exact superpose eq17483 eq15
    | exact resolve eq15 eq17483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18076 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17994 X0 X1
       have i₂ := eq17483 X0 X1
       grind)
    | exact superpose eq17483 eq17994
    | exact resolve eq17994 eq17483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17483 eq17994
  have eq20491 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18076 x y
       grind)
    | exact superpose eq18076 eq16
    | (have r₁ := eq16
       have r₂ := eq18076 x y
       grind)
    | exact resolve eq16 eq18076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18076
  have eq20561 : False := by grind
  exact eq20561

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq2388 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq2389 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2388 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388
  have eq17068 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2389 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2389
    | exact resolve eq2389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq17163 : ∀ X0 X1 X2 : G, (k (σ (k (τ X1) X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17068 X0 X1 X2
       have i₂ := eq18 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq18 eq17068
    | (have j0 := eq17068 X0 X1 X2
       grind)
    | exact resolve eq17068 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17068
  have eq17178 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17163 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq17163
    | (have j0 := eq17163 X0 X1 X2
       grind)
    | exact resolve eq17163 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq17163
  have eq17179 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17178 X0 X1 X2
       have j1 := eq12 (k X1 (σ X2)) X0
       grind)
    | (have r₁ := eq17178 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq17178 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17178
  have eq17210 : ∀ X0 X2 : G, (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq17179 X0 X0 (σ (σ (σ (σ (σ (M.op x x))))))
       have i₂ := eq391 X0 x
       grind)
    | exact superpose eq391 eq17179
    | exact resolve eq17179 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq17179
  have eq17713 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq17210 (σ X0) (σ X1)
       grind)
    | exact superpose eq17210 eq15
    | exact resolve eq15 eq17210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17795 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17713 X0 X1
       have i₂ := eq17210 X0 X1
       grind)
    | exact superpose eq17210 eq17713
    | exact resolve eq17713 eq17210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17210 eq17713
  have eq20185 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17795 x y
       grind)
    | exact superpose eq17795 eq16
    | (have r₁ := eq16
       have r₂ := eq17795 x y
       grind)
    | exact resolve eq16 eq17795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17795
  have eq20255 : False := by grind
  exact eq20255

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_x_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X0) X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X1) X0
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq31
    | exact resolve eq31 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq46
  have eq54 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (τ X0)
       grind)
    | exact superpose eq44 eq17
    | exact resolve eq17 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq55 (τ X0) X1
       grind)
    | exact superpose eq55 eq17
    | exact resolve eq17 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq60 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq64
    | exact resolve eq64 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq64 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq64 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq110 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq109 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq119 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq112 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq112 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq129 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq60 (τ X0) X1
       grind)
    | exact superpose eq60 eq17
    | exact resolve eq17 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq60
  have eq132 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq129
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq148 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (σ X0)
       grind)
    | exact superpose eq44 eq28
    | exact resolve eq28 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq169 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (τ (M.op X1 X1))
       have i₂ := eq161 (σ X0) X1
       grind)
    | exact superpose eq161 eq28
    | exact resolve eq28 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq175 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq169
    | exact resolve eq169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq276 : ∀ X0 X1 : G, (σ (σ (σ (σ (M.op X0 X0))))) ≠ (σ (σ (σ (σ (M.op X0 X0))))) ∨ (k X1 (σ (σ (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ (σ (σ (M.op X0 X0)))) X1
       have i₂ := eq132 (σ (σ (σ (M.op X0 X0)))) X0
       grind)
    | exact superpose eq132 eq119
    | (have j0 := eq119 (σ (σ (σ (M.op X0 X0)))) X1
       grind)
    | exact resolve eq119 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq278 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq352 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (M.op X0 X0)))))) ≠ (σ (σ (σ (σ (σ (M.op X0 X0)))))) ∨ (k X1 (σ (σ (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ (σ (σ (σ (M.op X0 X0))))) X1
       have i₂ := eq278 X0 (σ (σ (σ (σ (M.op X0 X0)))))
       grind)
    | exact superpose eq278 eq119
    | (have j0 := eq119 (σ (σ (σ (σ (M.op X0 X0))))) X1
       grind)
    | exact resolve eq119 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq358 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq352 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq443 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) ≠ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) ∨ (k X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1
       have i₂ := eq358 X0 (σ (σ (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq358 eq119
    | (have j0 := eq119 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1
       grind)
    | exact resolve eq119 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq450 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq443 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq610 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) ≠ (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) ∨ (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) X1
       have i₂ := eq450 X0 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))
       grind)
    | exact superpose eq450 eq119
    | (have j0 := eq119 (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) X1
       grind)
    | exact resolve eq119 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq619 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq610 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq646 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq110 (τ (τ (M.op X0 X0)))
       have i₂ := eq175 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq175 eq110
    | (have j0 := eq110 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq110 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq175
  have eq657 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have j0 := eq646 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq673 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq657 X0
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq657
    | exact resolve eq657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq1536 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq68 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1537 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq1536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq1540 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1537 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1537
    | (have j0 := eq1537 X0
       grind)
    | exact resolve eq1537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq2545 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 (k X0 (σ X1)) (σ X2)
       have i₂ := eq96 X0 X1 X2
       grind)
    | exact superpose eq96 eq48
    | (have j1 := eq96 X0 X1 X2
       grind)
    | (have r₁ := eq48 (k X0 (σ X1)) (σ X2)
       have r₂ := eq96 X0 X1 X2
       grind)
    | (have r₁ := eq48 (k X0 (σ X1)) (k X0 (σ X1))
       have r₂ := eq96 X0 X1 X2
       grind)
    | exact resolve eq48 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq2548 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X0 (σ X1)) (σ X2)
       have i₂ := eq96 X0 X1 X2
       grind)
    | exact superpose eq96 eq31
    | (have j1 := eq96 X0 X1 X2
       grind)
    | exact resolve eq31 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq96
  have eq2549 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2548 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq2553 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2545 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545
  have eq2554 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2553 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq2555 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2554 X0 X1 X2
       have j1 := eq12 (k X0 (σ X1)) (k X0 (σ X1))
       grind)
    | (have r₁ := eq2554 X0 X1 X2
       have r₂ := eq12 X0 (k X0 (σ X1))
       grind)
    | exact resolve eq2554 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq6216 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1540 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1540
    | exact resolve eq1540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq6273 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6216 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6216
    | (have j0 := eq6216 X0
       grind)
    | exact resolve eq6216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6216
  have eq6966 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq6273 X0
       grind)
    | exact superpose eq6273 eq10
    | (have j1 := eq6273 X0
       grind)
    | exact resolve eq10 eq6273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6273
  have eq7032 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6966 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6966
    | (have j0 := eq6966 X0
       grind)
    | exact resolve eq6966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6966
  have eq7122 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq7032 X0
       grind)
    | exact superpose eq7032 eq43
    | (have j1 := eq7032 X0
       grind)
    | exact resolve eq43 eq7032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq7032
  have eq9108 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (τ (M.op X0 X0)) X1
       have i₂ := eq673 X0
       grind)
    | exact superpose eq673 eq32
    | exact resolve eq32 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq30555 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2549 X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) X2
       have i₂ := eq619 X0 X1
       grind)
    | exact superpose eq619 eq2549
    | exact resolve eq2549 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549
  have eq30639 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq30555 X0 x X2
       have i₂ := eq450 x (τ X0)
       grind)
    | exact superpose eq450 eq30555
    | (have j0 := eq30555 X0 x X2
       grind)
    | exact resolve eq30555 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30555
  have eq30662 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k (σ X2) X0) = (M.op (σ X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq30639 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq30639
    | (have j0 := eq30639 X0 X2
       grind)
    | exact resolve eq30639 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30639
  have eq31035 : ∀ X0 X1 X2 : G, (k X0 X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2555 X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) X2
       have i₂ := eq619 X0 X1
       grind)
    | exact superpose eq619 eq2555
    | exact resolve eq2555 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq2555
  have eq31201 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq31035 X0 x X2
       have i₂ := eq450 x (τ X0)
       grind)
    | exact superpose eq450 eq31035
    | (have j0 := eq31035 X0 x X2
       grind)
    | exact resolve eq31035 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq31035
  have eq31239 : ∀ X0 X2 : G, (k X0 X0) = X0 ∨ (k (σ X2) X0) = (M.op (σ X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq31201 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq31201
    | (have j0 := eq31201 X0 X2
       grind)
    | exact resolve eq31201 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31201
  have eq34997 : ∀ X0 X1 X2 : G, (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq30662 X0 X2
       grind)
    | exact superpose eq30662 eq44
    | (have j1 := eq30662 X0 X2
       grind)
    | exact resolve eq44 eq30662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq30662
  have eq35209 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq31239 (σ X0) X1
       grind)
    | exact superpose eq31239 eq28
    | (have j1 := eq31239 (σ X0) X1
       grind)
    | exact resolve eq28 eq31239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq35241 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31239 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31239
  have eq35271 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35241 X0
       have j1 := eq7122 (σ X0) x
       grind)
    | (have r₁ := eq35241 X0
       have r₂ := eq7122 (σ X0) (σ X0)
       grind)
    | exact resolve eq35241 eq7122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7122 eq35241
  have eq35294 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35209 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35209
    | (have j0 := eq35209 X0 X1
       grind)
    | exact resolve eq35209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35209
  have eq35321 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35271 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq35271
    | exact resolve eq35271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35271
  have eq35343 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35294 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq35294
    | (have j0 := eq35294 X0 X1
       grind)
    | exact resolve eq35294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35294
  have eq35470 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35321 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35321
    | exact resolve eq35321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35599 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq35321 X0
       grind)
    | exact superpose eq35321 eq32
    | exact resolve eq32 eq35321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35647 : ∀ X0 X1 : G, (M.op X1 (τ (σ (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9108 (σ X0) X1
       have i₂ := eq35321 X0
       grind)
    | exact superpose eq35321 eq9108
    | exact resolve eq9108 eq35321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9108 eq35321
  have eq35676 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35647 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq35647
    | exact resolve eq35647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35647
  have eq35735 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq35470 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq35470
    | exact resolve eq35470 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35470
  have eq35753 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq35735 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35735
    | exact resolve eq35735 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35735
  have eq57062 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34997 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34997
    | (have j0 := eq34997 X1 X2 X2
       grind)
    | exact resolve eq34997 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34997
  have eq141876 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35343 y x
       grind)
    | exact superpose eq35343 eq16
    | (have j1 := eq35343 y x
       grind)
    | exact resolve eq16 eq35343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35343
  have eq142123 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq141876
       have i₂ := eq35753 y
       grind)
    | exact superpose eq35753 eq141876
    | exact resolve eq141876 eq35753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35753 eq141876
  have eq144551 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq142123
       have i₂ := eq57062 x y X0
       grind)
    | exact superpose eq57062 eq142123
    | (have j1 := eq57062 X0 y X0
       grind)
    | exact resolve eq142123 eq57062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57062 eq142123
  have eq144572 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq144551 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144551
  have eq144575 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq144572 X0
       have j1 := eq12 X0 y
       grind)
    | (have r₁ := eq144572 X0
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq144572 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144572
  have eq145903 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq35599 y X0
       have i₂ := eq144575 y
       grind)
    | exact superpose eq144575 eq35599
    | exact resolve eq35599 eq144575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35599
  have eq145927 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq35676 y X0
       have i₂ := eq144575 y
       grind)
    | exact superpose eq144575 eq35676
    | exact resolve eq35676 eq144575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35676 eq144575
  have eq148389 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145903 (σ x)
       grind)
    | exact superpose eq145903 eq16
    | exact resolve eq16 eq145903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145903
  have eq148406 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq148389
       have i₂ := eq145927 x
       grind)
    | exact superpose eq145927 eq148389
    | exact resolve eq148389 eq145927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145927 eq148389
  have eq148407 : False := by grind
  exact eq148407

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_x_y_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X0) X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X1) X0
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq31
    | exact resolve eq31 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (τ X0)
       grind)
    | exact superpose eq44 eq17
    | exact resolve eq17 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq57 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq53 (τ X0) X1
       grind)
    | exact superpose eq53 eq17
    | exact resolve eq17 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq58 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq62
    | exact resolve eq62 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq100 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq62 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq62 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq106 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq105 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq115 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq108 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq108 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq125 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq58 (τ X0) X1
       grind)
    | exact superpose eq58 eq17
    | exact resolve eq17 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq58
  have eq128 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq125
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq144 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (σ X0)
       grind)
    | exact superpose eq44 eq28
    | exact resolve eq28 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq157 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144
    | exact resolve eq144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq165 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (τ (M.op X1 X1))
       have i₂ := eq157 (σ X0) X1
       grind)
    | exact superpose eq157 eq28
    | exact resolve eq28 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq157
  have eq171 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165
    | exact resolve eq165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq272 : ∀ X0 X1 : G, (σ (σ (σ (σ (M.op X0 X0))))) ≠ (σ (σ (σ (σ (M.op X0 X0))))) ∨ (k X1 (σ (σ (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ (σ (σ (M.op X0 X0)))) X1
       have i₂ := eq128 (σ (σ (σ (M.op X0 X0)))) X0
       grind)
    | exact superpose eq128 eq115
    | (have j0 := eq115 (σ (σ (σ (M.op X0 X0)))) X1
       grind)
    | exact resolve eq115 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq274 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq348 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (M.op X0 X0)))))) ≠ (σ (σ (σ (σ (σ (M.op X0 X0)))))) ∨ (k X1 (σ (σ (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ (σ (σ (σ (M.op X0 X0))))) X1
       have i₂ := eq274 X0 (σ (σ (σ (σ (M.op X0 X0)))))
       grind)
    | exact superpose eq274 eq115
    | (have j0 := eq115 (σ (σ (σ (σ (M.op X0 X0))))) X1
       grind)
    | exact resolve eq115 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq354 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq439 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) ≠ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) ∨ (k X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1
       have i₂ := eq354 X0 (σ (σ (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq354 eq115
    | (have j0 := eq115 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1
       grind)
    | exact resolve eq115 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq439 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq642 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq106 (τ (τ (M.op X0 X0)))
       have i₂ := eq171 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq171 eq106
    | (have j0 := eq106 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq106 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq171
  have eq653 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have j0 := eq642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq669 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq653 X0
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq653
    | exact resolve eq653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq1532 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq66 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1533 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq1532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1536 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1533 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1533
    | (have j0 := eq1533 X0
       grind)
    | exact resolve eq1533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1640 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq94
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1641 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1640
  have eq2354 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (k X0 (σ X1)) (σ X2)
       have i₂ := eq92 X0 X1 X2
       grind)
    | exact superpose eq92 eq46
    | (have j1 := eq92 X0 X1 X2
       grind)
    | (have r₁ := eq46 (k X0 (σ X1)) (σ X2)
       have r₂ := eq92 X0 X1 X2
       grind)
    | (have r₁ := eq46 (k X0 (σ X1)) (k X0 (σ X1))
       have r₂ := eq92 X0 X1 X2
       grind)
    | exact resolve eq46 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq92
  have eq2362 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2354 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq2363 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2362 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2364 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2363 X0 X1 X2
       have j1 := eq12 (k X0 (σ X1)) (k X0 (σ X1))
       grind)
    | (have r₁ := eq2363 X0 X1 X2
       have r₂ := eq12 X0 (k X0 (σ X1))
       grind)
    | exact resolve eq2363 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363
  have eq6011 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1536 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1536
    | exact resolve eq1536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq6068 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6011 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6011
    | (have j0 := eq6011 X0
       grind)
    | exact resolve eq6011 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6011
  have eq6927 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq6068 X0
       grind)
    | exact superpose eq6068 eq10
    | (have j1 := eq6068 X0
       grind)
    | exact resolve eq10 eq6068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6068
  have eq6994 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6927 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6927
    | (have j0 := eq6927 X0
       grind)
    | exact resolve eq6927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927
  have eq7367 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq6994 X0
       grind)
    | exact superpose eq6994 eq43
    | (have j1 := eq6994 X0
       grind)
    | exact resolve eq43 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6994
  have eq9212 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (τ (M.op X0 X0)) X1
       have i₂ := eq669 X0
       grind)
    | exact superpose eq669 eq32
    | exact resolve eq32 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq669
  have eq9764 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9212 (τ (M.op X0 X0)) X1
       have i₂ := eq9212 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq9212 eq9212
    | exact resolve eq9212 eq9212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25402 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq1641
       grind)
    | exact superpose eq1641 eq31
    | exact resolve eq31 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1641
  have eq25403 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq25402
  have eq29653 : ∀ X0 X1 X2 : G, (k X0 X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (M.op X1 X1))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2364 X1 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X2
       have i₂ := eq446 X0 X1
       grind)
    | exact superpose eq446 eq2364
    | exact resolve eq2364 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq2364
  have eq29818 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq29653 X0 x X2
       have i₂ := eq354 x (τ X0)
       grind)
    | exact superpose eq354 eq29653
    | (have j0 := eq29653 X0 x X2
       grind)
    | exact resolve eq29653 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq29653
  have eq29855 : ∀ X0 X2 : G, (k X0 X0) = X0 ∨ (k (σ X2) X0) = (M.op (σ X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq29818 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq29818
    | (have j0 := eq29818 X0 X2
       grind)
    | exact resolve eq29818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29818
  have eq35358 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29855 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29855
  have eq35382 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35358 X0
       have j1 := eq7367 (σ X0) x
       grind)
    | (have r₁ := eq35358 X0
       have r₂ := eq7367 (σ X0) (σ X0)
       grind)
    | exact resolve eq35358 eq7367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7367 eq35358
  have eq35432 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35382 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq35382
    | exact resolve eq35382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35382
  have eq35512 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35432 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35432
    | exact resolve eq35432 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35691 : ∀ X0 X1 : G, (M.op X1 (τ (σ (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9212 (σ X0) X1
       have i₂ := eq35432 X0
       grind)
    | exact superpose eq35432 eq9212
    | exact resolve eq9212 eq35432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9212
  have eq35693 : ∀ X0 X1 : G, (M.op X1 (τ (τ (σ (k X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9764 (σ X0) X1
       have i₂ := eq35432 X0
       grind)
    | exact superpose eq35432 eq9764
    | exact resolve eq9764 eq35432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9764
  have eq35720 : ∀ X0 X1 : G, (M.op X1 (τ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35693 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq35693
    | exact resolve eq35693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35693
  have eq35722 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35691 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq35691
    | exact resolve eq35691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35691
  have eq35781 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq35512 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq35512
    | exact resolve eq35512 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35512
  have eq35799 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq35781 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35781
    | exact resolve eq35781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35781
  have eq36795 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq35799 X0
       grind)
    | exact superpose eq35799 eq115
    | (have j0 := eq115 X0 X1
       grind)
    | exact resolve eq115 eq35799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq154834 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34 (σ y) (σ x)
       have i₂ := eq25403
       grind)
    | exact superpose eq25403 eq34
    | exact resolve eq34 eq25403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq25403
  have eq154844 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq154834
  have eq154854 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq154844
       have i₂ := eq35432 y
       grind)
    | exact superpose eq35432 eq154844
    | exact resolve eq154844 eq35432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35432 eq154844
  have eq154869 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq154854
       have i₂ := eq35799 y
       grind)
    | exact superpose eq35799 eq154854
    | exact resolve eq154854 eq35799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35799 eq154854
  have eq158400 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq36795 y X0
       have i₂ := eq154869
       grind)
    | exact superpose eq154869 eq36795
    | (have j0 := eq36795 y X0
       grind)
    | (have r₁ := eq36795 y x
       have r₂ := eq154869
       grind)
    | exact resolve eq36795 eq154869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154869
  have eq158416 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq158400 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158400
  have eq158422 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq158416 X0
       have j1 := eq36795 y X0
       grind)
    | (have r₁ := eq158416 X0
       have r₂ := eq36795 y x
       grind)
    | exact resolve eq158416 eq36795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36795 eq158416
  have eq159500 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35720 (σ y) X0
       have i₂ := eq158422 (σ y)
       grind)
    | exact superpose eq158422 eq35720
    | exact resolve eq35720 eq158422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35720
  have eq159502 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq35722 (σ y) X0
       have i₂ := eq158422 (σ y)
       grind)
    | exact superpose eq158422 eq35722
    | exact resolve eq35722 eq158422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35722 eq158422
  have eq159659 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq159500 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq159500
    | exact resolve eq159500 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159500
  have eq161802 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq159502 (σ x)
       grind)
    | exact superpose eq159502 eq16
    | exact resolve eq16 eq159502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159502
  have eq161829 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq161802
       have i₂ := eq159659 x
       grind)
    | exact superpose eq159659 eq161802
    | exact resolve eq161802 eq159659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159659 eq161802
  have eq161830 : False := by grind
  exact eq161830

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X1) X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq19
    | exact resolve eq19 eq20
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
  have eq62 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
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
  have eq66 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq66 (τ X0) X1
       grind)
    | exact superpose eq66 eq17
    | exact resolve eq17 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq86 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq79 (τ X0) X1
       grind)
    | exact superpose eq79 eq17
    | exact resolve eq17 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq112 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (σ X0)
       grind)
    | exact superpose eq33 eq94
    | exact resolve eq94 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq125 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112
    | exact resolve eq112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq130 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq69
    | (have j0 := eq69 X2 X2
       grind)
    | exact resolve eq69 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq69 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq69 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq155 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq158 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq155 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq155 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq232 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq87 (τ X0) X1
       grind)
    | exact superpose eq87 eq17
    | exact resolve eq17 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq234 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq232
    | exact resolve eq232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq302 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq234 (τ X0) X1
       grind)
    | exact superpose eq234 eq17
    | exact resolve eq17 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq306 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302
    | exact resolve eq302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq385 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))
       have i₂ := eq306 (τ X0) X1
       grind)
    | exact superpose eq306 eq17
    | exact resolve eq17 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq389 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq385
    | exact resolve eq385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq503 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))
       have i₂ := eq389 (τ X0) X1
       grind)
    | exact superpose eq389 eq17
    | exact resolve eq17 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq503
    | exact resolve eq503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq729 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq158 (M.op X0 X0) X1
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq158
    | (have j0 := eq158 (M.op X0 X0) X1
       grind)
    | exact resolve eq158 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq760 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq777 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq760 X0 X1
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq760
    | exact resolve eq760 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq760
  have eq815 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ (M.op X1 X1)) X0
       have i₂ := eq777 X1 X0
       grind)
    | exact superpose eq777 eq19
    | exact resolve eq19 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq2172 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (k X0 (σ X1)) (σ X2)
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq19
    | (have j1 := eq130 X0 X1 X2
       grind)
    | exact resolve eq19 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq130
  have eq45460 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k (k (τ X0) (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2172 X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))) X2
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq2172
    | (have j0 := eq2172 X0 X1 X2
       grind)
    | exact resolve eq2172 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq2172
  have eq45544 : ∀ X0 X2 : G, (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (M.op X0 X0) = X0 ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq45460 X0 x X2
       have i₂ := eq389 (τ X0) x
       grind)
    | exact superpose eq389 eq45460
    | (have j0 := eq45460 X0 x X2
       grind)
    | exact resolve eq45460 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq45460
  have eq45566 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (M.op X0 X0) = X0 ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq45544 X0 X2
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq45544
    | (have j0 := eq45544 X0 X2
       grind)
    | exact resolve eq45544 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq45544
  have eq45588 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq45566 X0 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq45566 x X2
       have r₂ := eq12 X0 x
       grind)
    | (have r₁ := eq45566 X0 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq45566 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45566
  have eq45596 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45588 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45588
    | (have j0 := eq45588 X1 x
       grind)
    | exact resolve eq45588 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45588
  have eq45894 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq45596 X2 X0
       grind)
    | exact superpose eq45596 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq45596 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq45596 X0 X1
       grind)
    | exact resolve eq12 eq45596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45897 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq45596 X2 X0
       grind)
    | exact superpose eq45596 eq33
    | (have j1 := eq45596 X2 X0
       grind)
    | exact resolve eq33 eq45596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq45902 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125 X1 X0
       have i₂ := eq45596 X2 X0
       grind)
    | exact superpose eq45596 eq125
    | (have j1 := eq45596 X2 X0
       grind)
    | exact resolve eq125 eq45596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq45596
  have eq45945 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq45894 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45894
  have eq47192 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq45897 X0 X2 (τ X1)
       grind)
    | exact superpose eq45897 eq18
    | (have j1 := eq45897 X0 X2 X2
       grind)
    | exact resolve eq18 eq45897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45897
  have eq51118 : ∀ X0 X1 X2 : G, (k (σ X0) X2) = (M.op (σ X0) X2) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45902 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45902
    | (have j0 := eq45902 (σ X0) X1 X2
       grind)
    | exact resolve eq45902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45902
  have eq67803 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45945 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45945
  have eq67804 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67803 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67803
  have eq71547 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq51118 X0 X2 (σ X1)
       grind)
    | exact superpose eq51118 eq15
    | (have j1 := eq51118 X0 X2 X2
       grind)
    | exact resolve eq15 eq51118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51118
  have eq188603 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47192 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47192
    | (have j0 := eq47192 X1 X1 X2
       grind)
    | exact resolve eq47192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47192
  have eq189308 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188603 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq188603
    | (have j0 := eq188603 X0 X1 X2
       grind)
    | exact resolve eq188603 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188603
  have eq234342 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq71547 x y X0
       grind)
    | exact superpose eq71547 eq16
    | (have j1 := eq71547 x x X0
       grind)
    | exact resolve eq16 eq71547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71547
  have eq234635 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq234342 X0
       have j1 := eq189308 X0 x X0
       grind)
    | (have r₁ := eq234342 X0
       have r₂ := eq189308 y x x
       grind)
    | exact resolve eq234342 eq189308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189308 eq234342
  have eq235096 : x = (M.op x x) := by
    first
    | (have i₁ := eq67804 x
       have i₂ := eq234635 x
       grind)
    | exact superpose eq234635 eq67804
    | exact resolve eq67804 eq234635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67804 eq234635
  have eq236183 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq30 X0 x
       have i₂ := eq235096
       grind)
    | exact superpose eq235096 eq30
    | exact resolve eq30 eq235096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq236216 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq815 X0 x
       have i₂ := eq235096
       grind)
    | exact superpose eq235096 eq815
    | exact resolve eq815 eq235096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq235096
  have eq246824 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq236216 (σ y)
       grind)
    | exact superpose eq236216 eq16
    | exact resolve eq16 eq236216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236216
  have eq247023 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq246824
       have i₂ := eq236183 y
       grind)
    | exact superpose eq236183 eq246824
    | exact resolve eq246824 eq236183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236183 eq246824
  have eq247024 : False := by grind
  exact eq247024

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X1) X0
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq33
    | exact resolve eq33 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq56 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq34 X1 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq60 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (M.op X1 X1)
       have i₂ := eq34 X1 (σ X0)
       grind)
    | exact superpose eq34 eq89
    | exact resolve eq89 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
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
  have eq133 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq64 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq64 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq135 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) X1
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq21
    | (have j1 := eq64 X0 X0
       grind)
    | exact resolve eq21 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq144 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq143 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq150 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq151 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq152 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq154 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq151 X0
       have j1 := eq144 X0
       grind)
    | (have r₁ := eq151 X0
       have r₂ := eq144 X0
       grind)
    | exact resolve eq151 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq151
  have eq155 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq152 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq158 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq154 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq154
    | (have j0 := eq154 X0
       grind)
    | exact resolve eq154 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq165 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (τ (M.op X1 X1))
       have i₂ := eq121 (σ X0) X1
       grind)
    | exact superpose eq121 eq89
    | exact resolve eq89 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165
    | exact resolve eq165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq404 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (M.op (σ X0) X1) (σ X2)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 X1 X2
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq88
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq88 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq150 X0 X2
       grind)
    | exact superpose eq150 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq150 X0 X2
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq150 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ (k X0 X0))
       have r₂ := eq150 X0 (σ (k X0 X0))
       grind)
    | exact resolve eq12 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq638 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq620 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq729 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 (M.op X0 X0) X1
       have i₂ := eq34 X0 (M.op X0 X0)
       grind)
    | exact superpose eq34 eq155
    | (have j0 := eq155 (M.op X0 X0) X1
       grind)
    | exact resolve eq155 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq737 : ∀ X0 X1 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (k X1 (σ (τ (τ (M.op X0 X0))))) = (M.op X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 (τ (τ (M.op X0 X0))) X1
       have i₂ := eq169 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq169 eq155
    | (have j0 := eq155 (τ (τ (M.op X0 X0))) X1
       grind)
    | exact resolve eq155 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq746 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq155
    | (have j0 := eq155 (τ X0) X1
       grind)
    | exact resolve eq155 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq752 : ∀ X0 X1 : G, (k X1 (σ (τ (τ (M.op X0 X0))))) = (M.op X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq737 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq760 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq762 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq746 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq746
    | (have j0 := eq746 X0 X1
       grind)
    | exact resolve eq746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq769 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq752 X0 X1
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq752
    | exact resolve eq752 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq777 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq760 X0 X1
       have i₂ := eq60 X1 X0
       grind)
    | exact superpose eq60 eq760
    | exact resolve eq760 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq760
  have eq778 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq762
    | (have j0 := eq762 X0 X1
       grind)
    | exact resolve eq762 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq785 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq769 X0 X1
       have i₂ := eq121 X1 X0
       grind)
    | exact superpose eq121 eq769
    | exact resolve eq769 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq814 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ (M.op X1 X1)) X0
       have i₂ := eq777 X1 X0
       grind)
    | exact superpose eq777 eq20
    | exact resolve eq20 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq777
  have eq888 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq158 X0
       grind)
    | exact superpose eq158 eq10
    | (have j1 := eq158 X0
       grind)
    | exact resolve eq10 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq917 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq888 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq888
    | (have j0 := eq888 X0
       grind)
    | exact resolve eq888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq1749 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq778 (τ X0) X1
       have i₂ := eq92 X0 X0
       grind)
    | exact superpose eq92 eq778
    | (have j0 := eq778 (τ X0) X1
       grind)
    | exact resolve eq778 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5892 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X2 (σ (k X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq638 X1 X0 X2
       grind)
    | exact superpose eq638 eq59
    | (have j1 := eq638 X1 X1 X2
       grind)
    | exact resolve eq59 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq638
  have eq6178 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X1 (σ X0)
       have i₂ := eq917 X0
       grind)
    | exact superpose eq917 eq121
    | (have j1 := eq917 X0
       grind)
    | exact resolve eq121 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq6218 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6178 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6178
    | (have j0 := eq6178 X0 X1
       grind)
    | exact resolve eq6178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6178
  have eq10206 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq6218 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6218
  have eq10207 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq10206 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10206
  have eq22601 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq404
  have eq22632 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq22601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22601
  have eq22649 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22632 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22632
    | (have j0 := eq22632 X0
       grind)
    | exact resolve eq22632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22632
  have eq22726 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22649 X0
       have i₂ := eq10207 X0
       grind)
    | exact superpose eq10207 eq22649
    | (have j0 := eq22649 X0
       grind)
    | exact resolve eq22649 eq10207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10207 eq22649
  have eq128548 : ∀ X0 X1 X2 : G, (k X1 (k (τ (σ X0)) X0)) = X1 ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X1 (σ X0)
       have i₂ := eq5892 (σ X0) X0 X2
       grind)
    | exact superpose eq5892 eq121
    | (have j1 := eq5892 X0 X0 X2
       grind)
    | exact resolve eq121 eq5892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5892
  have eq128762 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (k X1 (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128548 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq128548
    | (have j0 := eq128548 X0 X1 X2
       grind)
    | exact resolve eq128548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128548
  have eq128958 : ∀ X0 X1 X2 : G, (k X1 (τ (σ (k X0 X0)))) = X1 ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X1 (σ (k X0 X0))
       have i₂ := eq128762 X0 X2 (σ (k X0 X0))
       grind)
    | exact superpose eq128762 eq121
    | (have j1 := eq128762 X0 X2 X2
       grind)
    | exact resolve eq121 eq128762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq128762
  have eq129038 : ∀ X0 X1 X2 : G, (k X1 (k X0 X0)) = X1 ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128958 X0 X1 X2
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq128958
    | (have j0 := eq128958 X0 X1 X1
       grind)
    | exact resolve eq128958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128958
  have eq130269 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq129038 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129038
  have eq130270 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq130269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130269
  have eq130457 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq778 (k X0 X0) X1
       have i₂ := eq130270 (k X0 X0) X0
       grind)
    | exact superpose eq130270 eq778
    | (have j0 := eq778 (k X0 X0) X1
       grind)
    | (have r₁ := eq778 (k X1 X1) X1
       have r₂ := eq130270 (k X1 X1) X1
       grind)
    | exact resolve eq778 eq130270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq130471 : ∀ X0 X1 : G, (τ (k X0 X0)) ≠ (τ (k X0 X0)) ∨ (k X1 (τ (k X0 X0))) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1749 (k X0 X0) X1
       have i₂ := eq130270 (k X0 X0) X0
       grind)
    | exact superpose eq130270 eq1749
    | (have j0 := eq1749 (k X0 X0) X1
       grind)
    | exact resolve eq1749 eq130270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq130702 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X2)) = (σ (k (k X0 (τ (k X1 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 (k X1 X1) X2
       have i₂ := eq130270 (σ X0) X1
       grind)
    | exact superpose eq130270 eq88
    | exact resolve eq88 eq130270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq130705 : ∀ X0 X1 X2 : G, (τ (k (σ X0) X2)) = (k (k X0 (τ (k X1 X1))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106 X0 (k X1 X1) X2
       have i₂ := eq130270 (σ X0) X1
       grind)
    | exact superpose eq130270 eq106
    | exact resolve eq106 eq130270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq130771 : ∀ X0 X1 : G, (k X1 (τ (k X0 X0))) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq130471 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130471
  have eq130772 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq130457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130457
  have eq130817 : ∀ X0 X1 X2 : G, (k X0 (τ X2)) = (k (k X0 (τ (k X1 X1))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130705 X0 X1 X2
       have i₂ := eq89 X0 X2
       grind)
    | exact superpose eq89 eq130705
    | exact resolve eq130705 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq130705
  have eq130820 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (k (k X0 (τ (k X1 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130702 X0 X1 X2
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq130702
    | exact resolve eq130702 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130702
  have eq130833 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq130772 X0 X1
       have i₂ := eq130270 X1 X0
       grind)
    | exact superpose eq130270 eq130772
    | exact resolve eq130772 eq130270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130270 eq130772
  have eq130871 : ∀ X0 X1 X2 : G, (k X0 (τ X2)) = (k (M.op X0 (τ (k X1 X1))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130817 X0 X1 X2
       have i₂ := eq130771 X1 X0
       grind)
    | exact superpose eq130771 eq130817
    | exact resolve eq130817 eq130771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130817
  have eq130873 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (k (M.op X0 (τ (k X1 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130820 X0 X1 X2
       have i₂ := eq130771 X1 X0
       grind)
    | exact superpose eq130771 eq130820
    | exact resolve eq130820 eq130771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130771 eq130820
  have eq131704 : ∀ X0 X1 : G, (M.op X1 (τ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq785 (k X0 X0) X1
       have i₂ := eq130833 X0 (k X0 X0)
       grind)
    | exact superpose eq130833 eq785
    | exact resolve eq785 eq130833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq130833
  have eq137818 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22726 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22726
    | exact resolve eq22726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22726
  have eq137973 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq137818 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq137818
    | (have j0 := eq137818 X0
       grind)
    | exact resolve eq137818 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq137818
  have eq137981 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq137973 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq137973
    | (have j0 := eq137973 X0
       grind)
    | exact resolve eq137973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137973
  have eq137982 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq137981 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq137981 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq137981 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137981
  have eq138577 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq137982 (σ X0)
       grind)
    | exact superpose eq137982 eq15
    | exact resolve eq15 eq137982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138609 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0 X0
       have i₂ := eq137982 (τ X0)
       grind)
    | exact superpose eq137982 eq92
    | exact resolve eq92 eq137982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq138669 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq138609 X0
       have i₂ := eq137982 X0
       grind)
    | exact superpose eq137982 eq138609
    | exact resolve eq138609 eq137982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138609
  have eq138677 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq138577 X0
       have i₂ := eq137982 X0
       grind)
    | exact superpose eq137982 eq138577
    | exact resolve eq138577 eq137982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137982 eq138577
  have eq164927 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (M.op (M.op X0 (τ (k X2 X2))) (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op X0 (τ (k X2 X2))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (τ (k X2 X2))) (τ X1)
       have i₂ := eq130871 X0 X2 X1
       grind)
    | exact superpose eq130871 eq14
    | (have j0 := eq14 (M.op X0 (τ (k X2 X2))) (τ X1)
       grind)
    | exact resolve eq14 eq130871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130871
  have eq164970 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op X0 (τ (k X2 X2))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq164927 X0 X1 X2
       have i₂ := eq131704 X2 X0
       grind)
    | exact superpose eq131704 eq164927
    | (have j0 := eq164927 X0 X1 X2
       grind)
    | exact resolve eq164927 eq131704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164927
  have eq165135 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op X0 (τ (k X2 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq164970 X0 X1 X2
       have j1 := eq12 X0 (τ X1)
       grind)
    | (have r₁ := eq164970 X0 X1 X2
       have r₂ := eq12 X0 (τ X1)
       grind)
    | exact resolve eq164970 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164970
  have eq165160 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq165135 X0 X1 x
       have i₂ := eq131704 x X0
       grind)
    | exact superpose eq131704 eq165135
    | (have j0 := eq165135 X0 X1 x
       grind)
    | exact resolve eq165135 eq131704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165135
  have eq165166 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165160 X0 X1
       have i₂ := eq138669 X1
       grind)
    | exact superpose eq138669 eq165160
    | (have j0 := eq165160 X0 X1
       grind)
    | exact resolve eq165160 eq138669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138669 eq165160
  have eq199658 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq165166 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165166
    | (have j0 := eq165166 X1 (σ X0)
       grind)
    | exact resolve eq165166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165166
  have eq200397 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq199658 X0 X1
       have i₂ := eq138677 X0
       grind)
    | exact superpose eq138677 eq199658
    | (have j0 := eq199658 X0 X1
       grind)
    | exact resolve eq199658 eq138677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199658
  have eq200420 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq200397 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq200397
    | (have j0 := eq200397 X0 X1
       grind)
    | exact resolve eq200397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200397
  have eq201905 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (M.op (M.op X0 (τ (k X1 X1))) X2)) ∨ (M.op X2 X2) = (M.op X0 (τ (k X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130873 X0 X1 X2
       have i₂ := eq200420 X2 (M.op X0 (τ (k X1 X1)))
       grind)
    | exact superpose eq200420 eq130873
    | (have j1 := eq200420 X2 (M.op X0 (τ (k X1 X1)))
       grind)
    | exact resolve eq130873 eq200420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130873
  have eq201941 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq200420 (σ X1) (σ X0)
       grind)
    | exact superpose eq200420 eq15
    | (have j1 := eq200420 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq200420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200420
  have eq202098 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq201941 X0 X1
       have i₂ := eq138677 X1
       grind)
    | exact superpose eq138677 eq201941
    | (have j0 := eq201941 X0 X1
       grind)
    | exact resolve eq201941 eq138677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138677 eq201941
  have eq202104 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = (M.op X0 (τ (k X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201905 X0 X1 X2
       have i₂ := eq131704 X1 X0
       grind)
    | exact superpose eq131704 eq201905
    | (have j0 := eq201905 X0 X1 X2
       grind)
    | exact resolve eq201905 eq131704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201905
  have eq202188 : ∀ X0 X2 : G, (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq202104 X0 x X2
       have i₂ := eq131704 x X0
       grind)
    | exact superpose eq131704 eq202104
    | (have j0 := eq202104 X0 x X2
       grind)
    | exact resolve eq202104 eq131704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131704 eq202104
  have eq1131242 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq202098 x y
       grind)
    | exact superpose eq202098 eq16
    | (have j1 := eq202098 x y
       grind)
    | exact resolve eq16 eq202098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202098
  have eq1133063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1131242
       have i₂ := eq202188 x y
       grind)
    | exact superpose eq202188 eq1131242
    | (have j1 := eq202188 x y
       grind)
    | (have r₁ := eq1131242
       have r₂ := eq202188 x y
       grind)
    | exact resolve eq1131242 eq202188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202188 eq1131242
  have eq1133064 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1133063
  have eq1134041 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 y
       have i₂ := eq1133064
       grind)
    | exact superpose eq1133064 eq31
    | exact resolve eq31 eq1133064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133064
  have eq1139107 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1134041 X0
       grind)
    | exact superpose eq1134041 eq10
    | (have j1 := eq1134041 X0
       grind)
    | exact resolve eq10 eq1134041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134041
  have eq1139857 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1139107 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1139107
    | (have j0 := eq1139107 X0
       grind)
    | exact resolve eq1139107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139107
  have eq1140234 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 y X0
       have i₂ := eq1139857 X1
       grind)
    | exact superpose eq1139857 eq21
    | (have j1 := eq1139857 X1
       grind)
    | exact resolve eq21 eq1139857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1139857
  have eq1145200 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1140234 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140234
  have eq1145201 : x = (M.op x x) := by grind
  clear eq1145200
  have eq1145212 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 x
       have i₂ := eq1145201
       grind)
    | exact superpose eq1145201 eq31
    | exact resolve eq31 eq1145201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1145244 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq814 X0 x
       have i₂ := eq1145201
       grind)
    | exact superpose eq1145201 eq814
    | exact resolve eq814 eq1145201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1145201
  have eq1189247 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1145244 (σ y)
       grind)
    | exact superpose eq1145244 eq16
    | exact resolve eq16 eq1145244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145244
  have eq1189621 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1189247
       have i₂ := eq1145212 y
       grind)
    | exact superpose eq1145212 eq1189247
    | exact resolve eq1189247 eq1145212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145212 eq1189247
  have eq1189622 : False := by grind
  exact eq1189622

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (M.op X1 X0) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq75 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq61 (M.op X1 X1) X0
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq61 X0 (M.op X0 X0)
       grind)
    | exact superpose eq61 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq61 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq340 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq393 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq394 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq393 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq503 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq340 X0 (M.op X1 X1)
       have i₂ := eq79 X1 (σ X0)
       grind)
    | exact superpose eq79 eq340
    | exact resolve eq340 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq525 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq503
    | exact resolve eq503 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq3308 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq394 (M.op X0 X0)
       have i₂ := eq79 X0 (M.op X0 X0)
       grind)
    | exact superpose eq79 eq394
    | (have j0 := eq394 (M.op X0 X0)
       grind)
    | exact resolve eq394 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3320 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq394 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq394
    | (have j0 := eq394 (τ X0)
       grind)
    | exact resolve eq394 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq394
  have eq3332 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3308 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq3337 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3320 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3320
    | (have j0 := eq3320 X0
       grind)
    | exact resolve eq3320 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq3347 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3337 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3337
    | (have j0 := eq3337 X0
       grind)
    | exact resolve eq3337 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337
  have eq18735 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ (M.op X0 X0)) X1
       have i₂ := eq3332 X0
       grind)
    | exact superpose eq3332 eq61
    | exact resolve eq61 eq3332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18737 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (σ (M.op X0 X0))
       have i₂ := eq3332 X0
       grind)
    | exact superpose eq3332 eq75
    | exact resolve eq75 eq3332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq19498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq19499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq19498
    | exact resolve eq19498 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19498
  have eq19510 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq19499
       have r₂ := eq28
       grind)
    | exact resolve eq19499 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19499
  have eq19521 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19510 eq525
    | exact resolve eq525 eq19510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19510
  have eq19542 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq19521
    | exact resolve eq19521 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19521
  have eq19543 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19542 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq19542 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq19542 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19542
  have eq19548 : ∀ X0 X1 : G, x = (M.op y y) ∨ (k X1 y) = X1 ∨ (M.op X0 (σ x)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq19543 (M.op X0 X0)
       grind)
    | exact superpose eq19543 eq61
    | (have j1 := eq19543 X1
       grind)
    | exact resolve eq61 eq19543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19568 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq65 X0 x
       have i₂ := eq19543 (M.op x X0)
       grind)
    | exact superpose eq19543 eq65
    | (have j1 := eq19543 X0
       grind)
    | exact resolve eq65 eq19543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19543
  have eq19571 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq19568
    | (have j0 := eq19568 X0
       grind)
    | exact resolve eq19568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19568
  have eq19597 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18737 y X1
       have i₂ := eq19571 X0
       grind)
    | exact superpose eq19571 eq18737
    | (have j1 := eq19571 X1
       grind)
    | exact resolve eq18737 eq19571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18737 eq19571
  have eq19607 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19597 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19597
    | (have j0 := eq19597 X0 X1
       grind)
    | exact resolve eq19597 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq23145 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27
       have i₂ := eq19607 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq19607 eq27
    | (have j1 := eq19607 (σ y) X0
       grind)
    | exact resolve eq27 eq19607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19607
  have eq23176 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq23145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23145
  have eq23233 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3347 y
       have i₂ := eq23176 y
       grind)
    | exact superpose eq23176 eq3347
    | (have j0 := eq3347 y
       grind)
    | (have r₁ := eq3347 y
       have r₂ := eq23176 y
       grind)
    | exact resolve eq3347 eq23176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23176
  have eq23270 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23233
  have eq23522 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18735 y X0
       have i₂ := eq23270
       grind)
    | exact superpose eq23270 eq18735
    | exact resolve eq18735 eq23270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18735 eq23270
  have eq23536 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23522 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23522
    | (have j0 := eq23522 X0
       grind)
    | exact resolve eq23522 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq23522
  have eq24387 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23536 eq27
    | (have j1 := eq23536 (σ x)
       grind)
    | exact resolve eq27 eq23536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23536
  have eq24389 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24387
  have eq24399 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq24389 eq28
    | exact resolve eq28 eq24389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24389
  have eq47829 : ∀ X0 X1 : G, x = (M.op x y) ∨ (k X0 y) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 y y
       have i₂ := eq19548 X0 X1
       grind)
    | exact superpose eq19548 eq65
    | (have j1 := eq19548 X1 X0
       grind)
    | exact resolve eq65 eq19548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq19548
  have eq47831 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ x = (M.op x y) ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47829 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47829
    | (have j0 := eq47829 X0 X1
       grind)
    | exact resolve eq47829 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47829
  have eq47924 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3347 y
       have i₂ := eq47831 y X0
       grind)
    | exact superpose eq47831 eq3347
    | (have j0 := eq3347 y
       have j1 := eq47831 X0 X0
       grind)
    | (have r₁ := eq3347 y
       have r₂ := eq47831 y x
       grind)
    | exact resolve eq3347 eq47831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47831
  have eq48000 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq47924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47924
  have eq48239 : ∀ X0 X1 : G, (M.op X1 (σ x)) = X1 ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 y X0
       have i₂ := eq48000 X1
       grind)
    | exact superpose eq48000 eq61
    | (have j1 := eq48000 X1
       grind)
    | exact resolve eq61 eq48000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48000
  have eq49299 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x y) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq48239 (M.op X1 X1) X1
       grind)
    | exact superpose eq48239 eq525
    | (have j1 := eq48239 x X1
       grind)
    | exact resolve eq525 eq48239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq48239
  have eq49321 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29 eq49299
    | (have j0 := eq49299 X0 x
       grind)
    | exact resolve eq49299 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq49299
  have eq51985 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq3347 x
       have i₂ := eq49321 x X0
       grind)
    | exact superpose eq49321 eq3347
    | (have j0 := eq3347 x
       have j1 := eq49321 X0 x
       grind)
    | (have r₁ := eq3347 x
       have r₂ := eq49321 x x
       grind)
    | exact resolve eq3347 eq49321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347 eq49321
  have eq52069 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq51985 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51985
  have eq56090 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ x = (M.op x y) ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 x X0
       have i₂ := eq52069 X1
       grind)
    | exact superpose eq52069 eq61
    | (have j1 := eq52069 X1
       grind)
    | exact resolve eq61 eq52069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq52069
  have eq56920 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq56090 X0 x
       grind)
    | exact superpose eq56090 eq19
    | (have j1 := eq56090 X0 x
       grind)
    | exact resolve eq19 eq56090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56090
  have eq56923 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq56920 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56920
  have eq56941 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq75 X0 x
       have i₂ := eq56923 x
       grind)
    | exact superpose eq56923 eq75
    | exact resolve eq75 eq56923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq56923
  have eq57050 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq56941 y
       grind)
    | exact superpose eq56941 eq19
    | (have j1 := eq56941 y
       grind)
    | exact resolve eq19 eq56941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq56941
  have eq57090 : x = (M.op x y) := by grind
  clear eq57050
  have eq57106 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq57090 eq21
    | exact resolve eq21 eq57090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq57090
  have eq57336 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq57106
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57106
    | exact resolve eq57106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq57106
  have eq57343 : False := by grind
  exact eq57343

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (M.op X1 X1) X0
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq32
    | exact resolve eq32 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq50 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49
    | (have j0 := eq49 X0
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq54 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq45 X1 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq58 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq64 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq65 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq33
    | (have j1 := eq47 X0
       grind)
    | exact resolve eq33 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq47 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq47 X0
       grind)
    | exact resolve eq12 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq107 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq103 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq123 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq142 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq154 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op X1 X1)
       have i₂ := eq45 X1 (σ X0)
       grind)
    | exact superpose eq45 eq29
    | exact resolve eq29 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154
    | exact resolve eq154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq194 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq107
    | (have j0 := eq107 (τ X0) X1
       grind)
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq199 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq194
    | (have j0 := eq194 X0 X1
       grind)
    | exact resolve eq194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq202 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq238 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq274 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq202 (τ X0) X1
       have i₂ := eq123 X0 X0
       grind)
    | exact superpose eq123 eq202
    | (have j0 := eq202 (τ X0) X1
       grind)
    | exact resolve eq202 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq754 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq101 X0 X2
       grind)
    | exact superpose eq101 eq33
    | (have j1 := eq101 X0 X2
       grind)
    | exact resolve eq33 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq878 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq913 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq878 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq878
    | (have j0 := eq878 X0
       grind)
    | exact resolve eq878 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq1635 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq142
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq142
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq142
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq142
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq142 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1636 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq1635
  have eq1785 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 (σ (k (τ X0) (τ X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq754 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq754
    | (have j0 := eq754 (k (τ X0) (τ X0)) X2 X2
       grind)
    | exact resolve eq754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq1824 : ∀ X0 X1 X2 : G, (M.op X2 (k (σ (τ X0)) X0)) = X2 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1785 X0 X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1785
    | (have j0 := eq1785 (k (σ (τ X0)) X0) X2 X2
       grind)
    | exact resolve eq1785 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1825 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 X0)) = X2 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1824 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1824
    | (have j0 := eq1824 (k X0 X0) X2 X2
       grind)
    | exact resolve eq1824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1856 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X2 ∨ (k X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1 (k X0 X0)
       have i₂ := eq1825 X0 X2 (k X0 X0)
       grind)
    | exact superpose eq1825 eq58
    | (have j1 := eq1825 X0 X2 X2
       grind)
    | exact resolve eq58 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1859 : ∀ X0 X1 X2 : G, (k X1 (τ (k X0 X0))) = X1 ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq166 X1 (k X0 X0)
       have i₂ := eq1825 X0 X2 (k X0 X0)
       grind)
    | exact superpose eq1825 eq166
    | (have j1 := eq1825 X0 X2 X2
       grind)
    | exact resolve eq166 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq2076 : ∀ X0 X1 X2 : G, (k X1 (k X0 (τ (σ X0)))) = X1 ∨ (M.op X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1859 (σ X0) X1 X2
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq1859
    | (have j0 := eq1859 (σ X0) X1 X2
       grind)
    | exact resolve eq1859 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq2122 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = X2 ∨ (k X1 (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2076 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2076
    | (have j0 := eq2076 X0 X1 X2
       grind)
    | exact resolve eq2076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076
  have eq2293 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (k y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2122 y X0 (σ x)
       grind)
    | exact superpose eq2122 eq16
    | (have j1 := eq2122 y X0 x
       grind)
    | exact resolve eq16 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2475 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq913 X0
       grind)
    | exact superpose eq913 eq45
    | (have j1 := eq913 X0
       grind)
    | exact resolve eq45 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq2476 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 X0
       have i₂ := eq913 X0
       grind)
    | exact superpose eq913 eq58
    | (have j1 := eq913 X0
       grind)
    | exact resolve eq58 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq913
  have eq2522 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ (M.op X0 X0)) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq33
    | exact resolve eq33 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2523 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 (σ (M.op X0 X0))
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq44
    | exact resolve eq44 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq65
  have eq2643 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2522 (k X0 X0) X1
       have i₂ := eq1825 X0 X2 (k X0 X0)
       grind)
    | exact superpose eq1825 eq2522
    | (have j1 := eq1825 (σ (k X0 X0)) X1 X2
       grind)
    | exact resolve eq2522 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq3390 : ∀ X0 X1 X2 : G, (M.op X1 (k (σ (τ X0)) X0)) = X1 ∨ (M.op X2 (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2643 (τ X0) X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq2643
    | (have j0 := eq2643 (k (σ (τ X0)) X0) X1 X1
       grind)
    | exact resolve eq2643 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2643
  have eq3431 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = X2 ∨ (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3390 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3390
    | (have j0 := eq3390 X0 X1 X2
       grind)
    | exact resolve eq3390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390
  have eq3721 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2523 (τ X0) X1
       have i₂ := eq3431 X0 X1 (τ X0)
       grind)
    | exact superpose eq3431 eq2523
    | (have j1 := eq3431 X0 X2 X2
       grind)
    | exact resolve eq2523 eq3431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523 eq3431
  have eq3736 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 X0)) = X2 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3721 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3721
    | (have j0 := eq3721 X0 X1 X2
       grind)
    | exact resolve eq3721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq3988 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq3736 X0 (k X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736
  have eq3989 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq3988 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988
  have eq4020 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq32 (k X0 X0) X0
       have i₂ := eq3989 X0
       grind)
    | exact superpose eq3989 eq32
    | exact resolve eq32 eq3989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3989
  have eq4143 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4020 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4020
    | exact resolve eq4020 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4144 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4020 (τ X0)
       have i₂ := eq123 X0 X0
       grind)
    | exact superpose eq123 eq4020
    | exact resolve eq4020 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq4020
  have eq12639 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq2475 X0 X1
       grind)
    | exact superpose eq2475 eq10
    | (have j1 := eq2475 X0 X1
       grind)
    | exact resolve eq10 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475
  have eq12708 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12639 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq12639
    | (have j0 := eq12639 X0 X1
       grind)
    | exact resolve eq12639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12639
  have eq19217 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1636
       grind)
    | exact superpose eq1636 eq16
    | exact resolve eq16 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq22871 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (k y y)) = X0 ∨ (k X1 (σ (k y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2293 X0
       have i₂ := eq1856 y X1 x
       grind)
    | exact superpose eq1856 eq2293
    | (have j0 := eq2293 X0
       have j1 := eq1856 y X1 x
       grind)
    | exact resolve eq2293 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856 eq2293
  have eq22872 : ∀ X0 X1 : G, (k X0 (k y y)) = X0 ∨ (k X1 (σ (k y y))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq22871 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22871
  have eq35706 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0
       have i₂ := eq2476 X0 X1
       grind)
    | exact superpose eq2476 eq106
    | (have j0 := eq106 X0
       have j1 := eq2476 X0 X1
       grind)
    | exact resolve eq106 eq2476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq2476
  have eq35905 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq35706 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq35706 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq35706 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35706
  have eq78312 : ∀ X0 : G, (σ (k y y)) = (M.op (σ (k y y)) (σ (k y y))) ∨ (k X0 (σ (k y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq4143 (k y y)
       have i₂ := eq22872 (k y y) x
       grind)
    | exact superpose eq22872 eq4143
    | (have j1 := eq22872 X0 X0
       grind)
    | exact resolve eq4143 eq22872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143 eq22872
  have eq78501 : ∀ X0 : G, (k X0 (σ (k y y))) = X0 := by
    intro X0
    first
    | (have j0 := eq78312 X0
       have j1 := eq12 X0 (σ (k y y))
       grind)
    | (have r₁ := eq78312 X0
       have r₂ := eq12 X0 (σ (k y y))
       grind)
    | exact resolve eq78312 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78312
  have eq78661 : (τ (σ (k y y))) = (M.op (τ (σ (k y y))) (τ (σ (k y y)))) := by
    first
    | (have i₁ := eq4144 (σ (k y y))
       have i₂ := eq78501 (σ (k y y))
       grind)
    | exact superpose eq78501 eq4144
    | exact resolve eq4144 eq78501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144 eq78501
  have eq78909 : (k y y) = (M.op (k y y) (k y y)) := by
    first
    | (have i₁ := eq78661
       have i₂ := eq10 (k y y)
       grind)
    | exact superpose eq10 eq78661
    | exact resolve eq78661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78661
  have eq84091 : ∀ X0 : G, (M.op X0 (k y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 (k y y) X0
       have i₂ := eq78909
       grind)
    | exact superpose eq78909 eq33
    | exact resolve eq33 eq78909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq84111 : ∀ X0 : G, (M.op X0 (σ (k y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2522 (k y y) X0
       have i₂ := eq78909
       grind)
    | exact superpose eq78909 eq2522
    | exact resolve eq2522 eq78909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522 eq78909
  have eq125437 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq551613 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq125437 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq125437
    | exact resolve eq125437 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq125437
  have eq551869 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq551613 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq551613
    | (have j0 := eq551613 X0
       grind)
    | exact resolve eq551613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551613
  have eq551969 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq551869 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq551869
    | (have j0 := eq551869 X0
       grind)
    | exact resolve eq551869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551869
  have eq551986 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq551969 X0
       have j1 := eq12708 X0 x
       grind)
    | (have r₁ := eq551969 X0
       have r₂ := eq12708 X0 X0
       grind)
    | exact resolve eq551969 eq12708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12708 eq551969
  have eq553002 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq551986 (σ X0)
       grind)
    | exact superpose eq551986 eq15
    | exact resolve eq15 eq551986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553346 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq553002 X0
       have i₂ := eq551986 X0
       grind)
    | exact superpose eq551986 eq553002
    | exact resolve eq553002 eq551986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551986 eq553002
  have eq604456 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19217
       have i₂ := eq553346 x
       grind)
    | exact superpose eq553346 eq19217
    | (have r₁ := eq19217
       have r₂ := eq553346 x
       grind)
    | exact resolve eq19217 eq553346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19217
  have eq604511 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq604456
  have eq604552 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq604511
       have i₂ := eq553346 y
       grind)
    | exact superpose eq553346 eq604511
    | exact resolve eq604511 eq553346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604511
  have eq945177 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq35905 y X0
       have i₂ := eq604552
       grind)
    | exact superpose eq604552 eq35905
    | (have j0 := eq35905 y X0
       grind)
    | (have r₁ := eq35905 y x
       have r₂ := eq604552
       grind)
    | exact resolve eq35905 eq604552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604552
  have eq945227 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq945177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945177
  have eq945233 : ∀ X0 : G, (σ x) = (σ y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq945227 X0
       have j1 := eq35905 y X0
       grind)
    | (have r₁ := eq945227 X0
       have r₂ := eq35905 y x
       grind)
    | exact resolve eq945227 eq35905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35905 eq945227
  have eq945239 : ∀ X0 : G, y = (τ (σ x)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq945233 X0
       grind)
    | exact superpose eq945233 eq10
    | (have j1 := eq945233 X0
       grind)
    | exact resolve eq10 eq945233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945233
  have eq945854 : ∀ X0 : G, x = y ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq945239 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq945239
    | (have j0 := eq945239 X0
       grind)
    | exact resolve eq945239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945239
  have eq949528 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq945854 X0
       grind)
    | exact superpose eq945854 eq16
    | (have j1 := eq945854 X0
       grind)
    | exact resolve eq16 eq945854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945854
  have eq949796 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq949528 X0
       grind)
    | (have r₁ := eq949528 X0
       have r₂ := eq553346 x
       grind)
    | exact resolve eq949528 eq553346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553346 eq949528
  have eq949929 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq274 (σ y) X0
       have i₂ := eq949796 (σ y)
       grind)
    | exact superpose eq949796 eq274
    | (have j0 := eq274 (σ y) X0
       grind)
    | exact resolve eq274 eq949796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq949796
  have eq950672 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq949929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949929
  have eq951089 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq950672 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq950672
    | exact resolve eq950672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950672
  have eq955493 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq84091 X0
       have i₂ := eq951089 y
       grind)
    | exact superpose eq951089 eq84091
    | exact resolve eq84091 eq951089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84091
  have eq955500 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq84111 X0
       have i₂ := eq951089 y
       grind)
    | exact superpose eq951089 eq84111
    | exact resolve eq84111 eq951089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84111 eq951089
  have eq965231 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq955500 (σ x)
       grind)
    | exact superpose eq955500 eq16
    | exact resolve eq16 eq955500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955500
  have eq965273 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq965231
       have i₂ := eq955493 x
       grind)
    | exact superpose eq955493 eq965231
    | exact resolve eq965231 eq955493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955493 eq965231
  have eq965274 : False := by grind
  exact eq965274
