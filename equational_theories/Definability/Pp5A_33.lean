import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pyx_Equation3926 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3926 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq35 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq31
  have eq108 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq337 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89 x y
       grind)
    | exact superpose eq89 eq16
    | (have j1 := eq89 x y
       grind)
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq108
    | (have j1 := eq89 X0 X0
       grind)
    | exact resolve eq108 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq351 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq89 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq351 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq354 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq340 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq356 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq363 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq354 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq354
    | (have j0 := eq354 X0
       grind)
    | exact resolve eq354 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq365 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq356 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq356
    | (have j0 := eq356 X0
       grind)
    | exact resolve eq356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq516 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq352 (M.op X0 X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq352
    | (have j0 := eq352 (M.op X0 X1)
       grind)
    | exact resolve eq352 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq352 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq352
    | (have j0 := eq352 (τ X0)
       grind)
    | exact resolve eq352 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq521 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq516 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq523 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq520 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq520
    | (have j0 := eq520 X0
       grind)
    | exact resolve eq520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq526 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq523 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq523
    | (have j0 := eq523 X0
       grind)
    | exact resolve eq523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq552 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 (k X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (k X0 (k X0 X0)) X1
       have i₂ := eq363 X0
       grind)
    | exact superpose eq363 eq89
    | (have j0 := eq89 X0 X0
       have j1 := eq363 X0
       grind)
    | exact resolve eq89 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq363
  have eq586 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq526 (τ X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq526
    | (have j0 := eq526 (τ X0)
       grind)
    | exact resolve eq526 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq521 X0 X1
       grind)
    | exact superpose eq521 eq37
    | exact resolve eq37 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq895 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq337
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq337
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq896 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq895
  have eq1171 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq365 X0
       grind)
    | exact superpose eq365 eq108
    | (have j1 := eq365 X0
       grind)
    | exact resolve eq108 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq365
  have eq1193 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1171 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1171
    | (have j0 := eq1171 X0
       grind)
    | exact resolve eq1171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1267 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1193 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1193
    | exact resolve eq1193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1283 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq1193 (τ X0)
       grind)
    | exact superpose eq1193 eq18
    | (have j1 := eq1193 (τ X0)
       grind)
    | exact resolve eq18 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1193
  have eq1289 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1283 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1283
    | (have j0 := eq1283 X0
       grind)
    | exact resolve eq1283 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1302 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1267 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq1267
    | (have j0 := eq1267 X0
       grind)
    | exact resolve eq1267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1305 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1289 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1289
    | (have j0 := eq1289 X0
       grind)
    | exact resolve eq1289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1317 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1305 X0
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq1305
    | (have j0 := eq1305 X0
       grind)
    | exact resolve eq1305 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1925 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (k X0 X0) X1
       have i₂ := eq1317 X0
       grind)
    | exact superpose eq1317 eq19
    | (have j1 := eq1317 X0
       grind)
    | exact resolve eq19 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1935 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k (σ X1) X0) = (k (σ X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1925 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1925
    | (have j0 := eq1925 X0 X1
       grind)
    | exact resolve eq1925 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq2535 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq586 (M.op X0 X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq586
    | (have j0 := eq586 (M.op X0 X1)
       grind)
    | exact resolve eq586 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq2546 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2535 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq15331 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq42 y x
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq42
    | exact resolve eq42 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq19018 : ∀ X0 : G, (σ X0) ≠ (k (σ X0) (σ X0)) ∨ (k (σ X0) (σ X0)) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1935 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935
  have eq19021 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X0)) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq19018 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq19018
    | (have j0 := eq19018 X0
       grind)
    | exact resolve eq19018 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19018
  have eq19058 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 (k (τ (σ X0)) X0))) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19021 X0
       have i₂ := eq22 (σ X0) X0 X0
       grind)
    | exact superpose eq22 eq19021
    | (have j0 := eq19021 X0
       grind)
    | exact resolve eq19021 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19021
  have eq19094 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19058 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19058
    | (have j0 := eq19058 X0
       grind)
    | exact resolve eq19058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19058
  have eq19130 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19094 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq19094
    | (have j0 := eq19094 X0
       grind)
    | exact resolve eq19094 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19094
  have eq29737 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19130 X0
       have i₂ := eq1302 X0
       grind)
    | exact superpose eq1302 eq19130
    | (have j1 := eq1302 X0
       grind)
    | (have r₁ := eq19130 X0
       have r₂ := eq1302 X0
       grind)
    | exact resolve eq19130 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq19130
  have eq29756 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq29737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29737
  have eq29757 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq29756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29756
  have eq30116 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (k X0 (k X0 X0))
       have i₂ := eq29757 X0
       grind)
    | exact superpose eq29757 eq15
    | exact resolve eq15 eq29757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29757
  have eq30210 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30116 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq30116
    | exact resolve eq30116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30116
  have eq79857 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq552 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq79858 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq79857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79857
  have eq79859 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq79858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79858
  have eq79866 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq79859 X0
       have i₂ := eq30210 X0 X0
       grind)
    | exact superpose eq30210 eq79859
    | (have j0 := eq79859 X0
       grind)
    | exact resolve eq79859 eq30210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30210 eq79859
  have eq80280 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42 (σ X0) (σ X0)
       have i₂ := eq79866 X0
       grind)
    | exact superpose eq79866 eq42
    | (have j1 := eq79866 X0
       grind)
    | exact resolve eq42 eq79866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80302 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq79866 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79866
  have eq80314 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80280 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq80280
    | (have j0 := eq80280 X0
       grind)
    | exact resolve eq80280 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80280
  have eq80357 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq80314 X0
       have j1 := eq80302 X0
       grind)
    | (have r₁ := eq80314 X0
       have r₂ := eq80302 X0
       grind)
    | exact resolve eq80314 eq80302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80302 eq80314
  have eq80685 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80357 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80357
    | exact resolve eq80357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81080 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq80685 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq80685
    | exact resolve eq80685 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq80685
  have eq81145 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq81080 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81080
    | exact resolve eq81080 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81080
  have eq81470 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 X0
       have i₂ := eq81145 (τ X0)
       grind)
    | exact superpose eq81145 eq64
    | exact resolve eq64 eq81145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq81552 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq81470 X0
       have i₂ := eq81145 X0
       grind)
    | exact superpose eq81145 eq81470
    | exact resolve eq81470 eq81145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81470
  have eq1005054 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2546 (σ y) (σ x)
       have i₂ := eq15331
       grind)
    | exact superpose eq15331 eq2546
    | exact resolve eq2546 eq15331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546 eq15331
  have eq1005287 : (τ (σ x)) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1005054
       have i₂ := eq81552 (σ x)
       grind)
    | exact superpose eq81552 eq1005054
    | exact resolve eq1005054 eq81552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81552 eq1005054
  have eq1005477 : (τ (σ x)) = (τ (σ (k x x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1005287
       have i₂ := eq80357 x
       grind)
    | exact superpose eq80357 eq1005287
    | exact resolve eq1005287 eq80357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005287
  have eq1005659 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1005477
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq1005477
    | exact resolve eq1005477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005477
  have eq1005786 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1005659
       have i₂ := eq81145 x
       grind)
    | exact superpose eq81145 eq1005659
    | exact resolve eq1005659 eq81145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005659
  have eq1005855 : x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1005786
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1005786
    | exact resolve eq1005786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005786
  have eq1005904 : x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq526 x
       grind)
    | (have r₁ := eq1005855
       have r₂ := eq526 x
       grind)
    | exact resolve eq1005855 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005855
  have eq1005932 : (σ x) = (σ (k y y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1005904
       have i₂ := eq80357 y
       grind)
    | exact superpose eq80357 eq1005904
    | exact resolve eq1005904 eq80357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80357 eq1005904
  have eq1005947 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1005932
       have i₂ := eq81145 y
       grind)
    | exact superpose eq81145 eq1005932
    | exact resolve eq1005932 eq81145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81145 eq1005932
  have eq1006174 : x = (k x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq42 y y
       have i₂ := eq1005947
       grind)
    | exact superpose eq1005947 eq42
    | exact resolve eq42 eq1005947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1005947
  have eq1006337 : x = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have j1 := eq526 x
       grind)
    | (have r₁ := eq1006174
       have r₂ := eq526 x
       grind)
    | exact resolve eq1006174 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq1006174
  have eq1006472 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq37 x x x
       have i₂ := eq1006337
       grind)
    | exact superpose eq1006337 eq37
    | exact resolve eq37 eq1006337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006337
  have eq1006860 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1006472 X0
       grind)
    | exact superpose eq1006472 eq10
    | (have j1 := eq1006472 X0
       grind)
    | exact resolve eq10 eq1006472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006472
  have eq1007594 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1006860 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1006860
    | (have j0 := eq1006860 X0
       grind)
    | exact resolve eq1006860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006860
  have eq1008234 : ∀ X0 X1 : G, x = (M.op x X0) ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 y y x
       have i₂ := eq1007594 X0
       grind)
    | exact superpose eq1007594 eq37
    | (have j1 := eq1007594 X0
       grind)
    | exact resolve eq37 eq1007594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1007594
  have eq1010972 : ∀ X0 : G, x ≠ x ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1008234 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008234
  have eq1010973 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1010972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010972
  have eq1013234 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq682 x x x
       have i₂ := eq1010973 x
       grind)
    | exact superpose eq1010973 eq682
    | exact resolve eq682 eq1010973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1013865 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1013234 (σ y)
       grind)
    | exact superpose eq1013234 eq16
    | exact resolve eq16 eq1013234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013234
  have eq1014488 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1013865
       have i₂ := eq1010973 y
       grind)
    | exact superpose eq1010973 eq1013865
    | exact resolve eq1013865 eq1010973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010973 eq1013865
  have eq1014489 : False := by grind
  exact eq1014489

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_x_pyx_Equation3926 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3926 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X0)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq63 X0 (M.op X1 X0) x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) X0
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq67 X0 X0
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq63 X1 X0 X0
       grind)
    | exact superpose eq63 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq67 X0 X0
       grind)
    | exact resolve eq13 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq63 X1 X0 X0
       grind)
    | exact superpose eq63 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq417 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 x (M.op X0 X1)
       have i₂ := eq63 X0 X1 x
       grind)
    | exact superpose eq63 eq86
    | exact resolve eq86 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq86 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq420 (τ X0)
       grind)
    | exact superpose eq420 eq18
    | exact resolve eq18 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq420
  have eq537 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 x (M.op X0 X1)
       have i₂ := eq63 X0 X1 x
       grind)
    | exact superpose eq63 eq14
    | (have j0 := eq14 (M.op X0 X1) X2
       grind)
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X0 X2))) = (M.op (M.op X1 X0) X3) ∨ (M.op X0 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X2 X0 X1 X3
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq546 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 X0 x
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq63
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq564 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq566 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq543 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq567 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq566 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq568 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq542 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq569 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq565 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq565 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq565 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq572 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq561
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq561
    | exact resolve eq561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq583 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X2 (M.op X0 X2))) ∨ (M.op X0 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq544 X0 X1 X2 x
       have i₂ := eq63 X1 X0 x
       grind)
    | exact superpose eq63 eq544
    | (have j0 := eq544 X0 X1 X2 x
       grind)
    | exact resolve eq544 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq596 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X2 ∨ (M.op X1 X0) = (M.op X1 (M.op X2 X0)) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq583 X0 X1 X2
       have i₂ := eq67 X2 X0
       grind)
    | exact superpose eq67 eq583
    | (have j0 := eq583 X0 X1 X2
       grind)
    | exact resolve eq583 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq620 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq569 (σ X0)
       grind)
    | exact superpose eq569 eq15
    | exact resolve eq15 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq569 (τ X0)
       grind)
    | exact superpose eq569 eq31
    | exact resolve eq31 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq626 X0
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq626
    | exact resolve eq626 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq639 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq620 X0
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq620
    | exact resolve eq620 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq620
  have eq689 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ X0) x
       have i₂ := eq639 X0
       grind)
    | exact superpose eq639 eq63
    | exact resolve eq63 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0) (σ X0)
       have i₂ := eq639 X0
       grind)
    | exact superpose eq639 eq67
    | exact resolve eq67 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq726 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X0) (τ X0) x
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq63
    | exact resolve eq63 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq689 (M.op X0 X1) X1
       have i₂ := eq63 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq63 eq689
    | exact resolve eq689 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq933 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq726 (M.op X0 X1) X1
       have i₂ := eq63 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq63 eq726
    | exact resolve eq726 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq12993 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq91
    | (have j0 := eq91 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq91 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq13042 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12993 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12993
  have eq13052 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13042 X0 X1
       have j1 := eq546 X0 X1 x
       grind)
    | (have r₁ := eq13042 X1 X1
       have r₂ := eq546 X1 X1 x
       grind)
    | (have r₁ := eq13042 X0 x
       have r₂ := eq546 X0 X1 x
       grind)
    | exact resolve eq13042 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq13042
  have eq25406 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = X0 ∨ (M.op X3 (M.op X0 X1)) = (M.op X3 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X0 X2 X3
       have i₂ := eq596 X0 X1 X2
       grind)
    | exact superpose eq596 eq63
    | (have j1 := eq596 X1 X3 X0
       grind)
    | exact resolve eq63 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq61016 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13052 X0 X1
       have i₂ := eq537 X0 X1 X1
       grind)
    | exact superpose eq537 eq13052
    | (have j0 := eq13052 X0 X1
       have j1 := eq537 X0 X1 X1
       grind)
    | exact resolve eq13052 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq13052
  have eq61102 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq61016 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61016
  have eq61221 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61102 X0 X1
       have i₂ := eq67 X1 X0
       grind)
    | exact superpose eq67 eq61102
    | (have j0 := eq61102 X0 X1
       grind)
    | exact resolve eq61102 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61102
  have eq62291 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 x
       have i₂ := eq61221 X0 X1
       grind)
    | exact superpose eq61221 eq63
    | (have j1 := eq61221 X0 X1
       grind)
    | exact resolve eq63 eq61221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62685 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62291 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62291
  have eq62689 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62685 X0 X1
       have j1 := eq61221 X0 X1
       grind)
    | (have r₁ := eq62685 X1 X0
       have r₂ := eq61221 X0 X1
       grind)
    | exact resolve eq62685 eq61221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61221 eq62685
  have eq62975 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq62689 (σ X0) X1
       grind)
    | exact superpose eq62689 eq22
    | (have j1 := eq62689 (σ X0) X1
       grind)
    | exact resolve eq22 eq62689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq63882 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62975 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62975
    | exact resolve eq62975 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63951 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (M.op (k (τ X0) X1) X2) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq933 (σ X0) X1 X2
       have i₂ := eq62975 X0 X1
       grind)
    | exact superpose eq62975 eq933
    | (have j1 := eq62975 X1 X0
       grind)
    | exact resolve eq933 eq62975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62975
  have eq64092 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63882 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq63882
    | (have j0 := eq63882 X0 X1
       grind)
    | exact resolve eq63882 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63882
  have eq64376 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) = (k (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) (k X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq438 (k X1 X0)
       have i₂ := eq64092 X0 X1
       grind)
    | exact superpose eq64092 eq438
    | (have j1 := eq64092 X0 X1
       grind)
    | exact resolve eq438 eq64092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq64092
  have eq64409 : ∀ X0 X1 : G, (σ (τ (M.op (M.op X0 X1) (M.op X0 X1)))) = (k (σ (τ (M.op (M.op X0 X1) (M.op X0 X1)))) (k X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64376 X0 X1
       have i₂ := eq633 (M.op X0 X1)
       grind)
    | exact superpose eq633 eq64376
    | (have j0 := eq64376 X0 X1
       grind)
    | exact resolve eq64376 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq64376
  have eq64628 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op (M.op X0 X1) (M.op X0 X1)) (k X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64409 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq11 eq64409
    | (have j0 := eq64409 X0 X1
       grind)
    | exact resolve eq64409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64409
  have eq64778 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (k X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64628 X0 X1
       have i₂ := eq63 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq63 eq64628
    | (have j0 := eq64628 X0 X1
       grind)
    | exact resolve eq64628 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64628
  have eq65014 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X1 X0) (M.op X0 X1)) ∨ (M.op (k X1 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) (k X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62689 (k X1 X0) (M.op X0 X1)
       have i₂ := eq64778 X0 X1
       grind)
    | exact superpose eq64778 eq62689
    | (have j0 := eq62689 (k X1 X0) (M.op X0 X1)
       have j1 := eq64778 (k X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq62689 eq64778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62689
  have eq65018 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (k X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65014 X0 X1
       have i₂ := eq63 X0 X1 (k X1 X0)
       grind)
    | exact superpose eq63 eq65014
    | (have j0 := eq65014 X0 X1
       grind)
    | exact resolve eq65014 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65014
  have eq65019 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq65018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65018
  have eq65401 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k (M.op X1 X0) X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65019 X0 (M.op X1 X0)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq65019
    | exact resolve eq65019 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65019
  have eq65531 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k (M.op X1 X0) X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65401 X0 X1
       have i₂ := eq63 X1 X0 X0
       grind)
    | exact superpose eq63 eq65401
    | (have j0 := eq65401 X0 X1
       grind)
    | exact resolve eq65401 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65401
  have eq69869 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (M.op (τ (k X0 X1)) X2) ∨ (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63951 X1 (τ X0) X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq63951
    | (have j0 := eq63951 X0 (τ X1) X2
       grind)
    | exact resolve eq63951 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63951
  have eq70257 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (M.op (τ (k X0 X1)) X2) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69869 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69869
    | (have j0 := eq69869 X0 X1 X2
       grind)
    | exact resolve eq69869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69869
  have eq70751 : ∀ X0 X1 X3 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X3) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq751 (τ (k X0 X1)) x x
       have i₂ := eq70257 X0 X1 x
       grind)
    | exact superpose eq70257 eq751
    | (have j1 := eq70257 X0 X1 x
       grind)
    | exact resolve eq751 eq70257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70257
  have eq70829 : ∀ X0 X1 X3 : G, (k X0 X1) = (M.op (k X0 X1) X3) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq70751 X0 X1 X3
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq70751
    | (have j0 := eq70751 X0 X1 X3
       grind)
    | exact resolve eq70751 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70751
  have eq94207 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X0) X0) ∨ (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70829 (M.op X1 X0) X0 (M.op X0 X1)
       have i₂ := eq65531 X0 X1
       grind)
    | exact superpose eq65531 eq70829
    | (have j0 := eq70829 X0 (M.op X1 X0) x
       have j1 := eq65531 X0 (M.op X1 X0)
       grind)
    | exact resolve eq70829 eq65531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65531 eq70829
  have eq94316 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X1) = (k (M.op X1 X0) X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq94207 X0 X1
       have i₂ := eq63 X1 X0 X0
       grind)
    | exact superpose eq63 eq94207
    | (have j0 := eq94207 X0 X1
       grind)
    | exact resolve eq94207 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94207
  have eq94377 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k (M.op X1 X0) X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq94316 X0 X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq94316
    | (have j0 := eq94316 X0 X1
       grind)
    | exact resolve eq94316 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq94316
  have eq94378 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X0) X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq94377 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94377
  have eq122669 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq25406 X0 X1 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122674 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq122669 X0 X1
       have j1 := eq25406 X0 X1 x X0
       grind)
    | (have r₁ := eq122669 X0 x
       have r₂ := eq25406 X0 X1 x x
       grind)
    | exact resolve eq122669 eq25406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25406 eq122669
  have eq122709 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq122674 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq122674
    | (have j0 := eq122674 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq122674 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122844 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1 X0
       have i₂ := eq122674 X0 X1
       grind)
    | exact superpose eq122674 eq417
    | (have j0 := eq417 X0 X1 X0
       have j1 := eq122674 X0 X1
       grind)
    | (have r₁ := eq417 X0 X1 X0
       have r₂ := eq122674 X0 X1
       grind)
    | exact resolve eq417 eq122674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq122674
  have eq123009 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq122844 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122844
  have eq123037 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq122709 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq122709 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq122709 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq122709 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122709
  have eq123052 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq123009 X0 X1
       have i₂ := eq567 X0 X1
       grind)
    | exact superpose eq567 eq123009
    | (have j0 := eq123009 X0 X1
       have j1 := eq567 X1 X0
       grind)
    | exact resolve eq123009 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq123341 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq123052 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123052
  have eq124055 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq123341 (σ X0) (σ X1)
       grind)
    | exact superpose eq123341 eq15
    | (have j1 := eq123341 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq123341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124076 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq123341 X0 (τ X1)
       grind)
    | exact superpose eq123341 eq17
    | (have j1 := eq123341 X0 (τ X1)
       grind)
    | exact resolve eq17 eq123341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq124094 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq123341 (τ X0) (τ X1)
       grind)
    | exact superpose eq123341 eq31
    | (have j1 := eq123341 (τ X0) (τ X1)
       grind)
    | exact resolve eq31 eq123341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123341
  have eq124223 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124094 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq124094
    | (have j0 := eq124094 X0 X1
       grind)
    | exact resolve eq124094 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq124094
  have eq124243 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124055 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq124055
    | (have j0 := eq124055 X0 X1
       grind)
    | exact resolve eq124055 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124055
  have eq125760 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq124076 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq124076
    | exact resolve eq124076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124076
  have eq126127 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq125760 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq125760
    | (have j0 := eq125760 X0 X1
       grind)
    | exact resolve eq125760 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125760
  have eq128420 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123009 X1 X0
       have i₂ := eq123037 X0 X1
       grind)
    | exact superpose eq123037 eq123009
    | (have j0 := eq123009 X1 X0
       have j1 := eq123037 X0 X1
       grind)
    | exact resolve eq123009 eq123037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123009 eq123037
  have eq128522 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq128420 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128420
  have eq129141 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq128522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128522
  have eq135894 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq124223 X0 X1
       grind)
    | exact superpose eq124223 eq11
    | (have j1 := eq124223 X0 X1
       grind)
    | exact resolve eq11 eq124223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124223
  have eq136042 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135894 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq135894
    | (have j0 := eq135894 X0 X1
       grind)
    | exact resolve eq135894 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135894
  have eq136828 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X2) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq751 (τ X0) (τ X1) X2
       have i₂ := eq136042 X0 X1
       grind)
    | exact superpose eq136042 eq751
    | (have j1 := eq136042 X1 X0
       grind)
    | exact resolve eq751 eq136042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136042
  have eq136988 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (k X0 X1) X2) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136828 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq136828
    | (have j0 := eq136828 X0 X1 X2
       grind)
    | exact resolve eq136828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136828
  have eq143805 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq124243 X0 X1
       grind)
    | exact superpose eq124243 eq10
    | (have j1 := eq124243 X0 X1
       grind)
    | exact resolve eq10 eq124243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124243
  have eq143883 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq143805 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq143805
    | (have j0 := eq143805 X0 X1
       grind)
    | exact resolve eq143805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143805
  have eq144524 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq143883 x y
       grind)
    | exact superpose eq143883 eq16
    | (have j1 := eq143883 x y
       grind)
    | exact resolve eq16 eq143883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143883
  have eq145191 : x = (k x y) := by
    first
    | (have j1 := eq126127 y x
       grind)
    | (have r₁ := eq144524
       have r₂ := eq126127 y x
       grind)
    | exact resolve eq144524 eq126127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126127 eq144524
  have eq145865 : x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq145191
       have i₂ := eq568 x y
       grind)
    | exact superpose eq568 eq145191
    | (have j1 := eq568 x y
       grind)
    | exact resolve eq145191 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq145892 : (M.op y x) = (k (M.op y x) x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq64778 y x
       have i₂ := eq145191
       grind)
    | exact superpose eq145191 eq64778
    | (have j0 := eq64778 x y
       grind)
    | exact resolve eq64778 eq145191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64778
  have eq145951 : ∀ X0 : G, y = (k y x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq136988 x y x
       have i₂ := eq145191
       grind)
    | exact superpose eq145191 eq136988
    | (have j0 := eq136988 x y x
       grind)
    | exact resolve eq136988 eq145191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136988
  have eq145953 : (M.op y x) = (k (M.op y x) x) := by
    first
    | (have j1 := eq86 x y
       grind)
    | (have r₁ := eq145892
       have r₂ := eq86 x y
       grind)
    | (have r₁ := eq145892
       have r₂ := eq86 y x
       grind)
    | exact resolve eq145892 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq145892
  have eq145954 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq145865
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq145865
       have r₂ := eq12 y x
       grind)
    | exact resolve eq145865 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145865
  have eq145955 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq145954
       have i₂ := eq145191
       grind)
    | exact superpose eq145191 eq145954
    | exact resolve eq145954 eq145191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145191 eq145954
  have eq145991 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq94378 x y
       have i₂ := eq145953
       grind)
    | exact superpose eq145953 eq94378
    | (have j0 := eq94378 x y
       grind)
    | exact resolve eq94378 eq145953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94378 eq145953
  have eq146071 : (M.op x y) = (M.op y x) := by grind
  clear eq145991
  have eq146190 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq146071
       grind)
    | exact superpose eq146071 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq146071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146299 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq146190
       have r₂ := eq145951 y
       grind)
    | exact resolve eq146190 eq145951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145951 eq146190
  have eq146303 : y = (k y x) := by
    first
    | (have j1 := eq129141 y x
       grind)
    | (have r₁ := eq146299
       have r₂ := eq129141 y x
       grind)
    | exact resolve eq146299 eq129141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129141 eq146299
  have eq147625 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq63 x y x
       have i₂ := eq145955
       grind)
    | exact superpose eq145955 eq63
    | exact resolve eq63 eq145955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq147633 : ∀ X0 : G, x = (M.op x y) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq751 x y x
       have i₂ := eq145955
       grind)
    | exact superpose eq145955 eq751
    | exact resolve eq751 eq145955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145955
  have eq149518 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq751 x y x
       have i₂ := eq147633 X0
       grind)
    | exact superpose eq147633 eq751
    | (have j1 := eq147633 X1
       grind)
    | exact resolve eq751 eq147633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147633
  have eq157376 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq149518 (σ y) X0
       grind)
    | exact superpose eq149518 eq16
    | (have j1 := eq149518 X0 X0
       grind)
    | exact resolve eq16 eq149518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149518
  have eq163227 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) X0) ∨ y = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq157376 X0
       have i₂ := eq147625 X1
       grind)
    | exact superpose eq147625 eq157376
    | (have j0 := eq157376 X0
       have j1 := eq147625 X1
       grind)
    | exact resolve eq157376 eq147625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147625 eq157376
  have eq163264 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op y X1) := by
    intro X0 X1
    first
    | (have j0 := eq163227 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163227
  have eq163444 : ∀ X1 X2 : G, (τ (σ y)) = (M.op (τ (σ y)) X1) ∨ y = (M.op y X2) := by
    intro X1 X2
    first
    | (have i₁ := eq933 (σ y) x X2
       have i₂ := eq163264 x X1
       grind)
    | exact superpose eq163264 eq933
    | (have j1 := eq163264 x X2
       grind)
    | exact resolve eq933 eq163264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq163264
  have eq163594 : ∀ X1 X2 : G, y = (M.op y X1) ∨ y = (M.op y X2) := by
    intro X1 X2
    first
    | (have i₁ := eq163444 X1 X2
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq163444
    | (have j0 := eq163444 X1 X1
       grind)
    | exact resolve eq163444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163444
  have eq164061 : ∀ X0 : G, y ≠ y ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq163594 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163594
  have eq164062 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq164061 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164061
  have eq164102 : y = (M.op x y) := by
    first
    | (have i₁ := eq146071
       have i₂ := eq164062 x
       grind)
    | exact superpose eq164062 eq146071
    | exact resolve eq146071 eq164062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146071
  have eq164250 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq751 y x x
       have i₂ := eq164062 x
       grind)
    | exact superpose eq164062 eq751
    | exact resolve eq751 eq164062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq164891 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq572
       have i₂ := eq164102
       grind)
    | exact superpose eq164102 eq572
    | exact resolve eq572 eq164102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq165026 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq164891
  have eq165050 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq165026
       have i₂ := eq146303
       grind)
    | exact superpose eq146303 eq165026
    | exact resolve eq165026 eq146303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146303 eq165026
  have eq165058 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq165050
       have i₂ := eq164250 (σ x)
       grind)
    | exact superpose eq164250 eq165050
    | exact resolve eq165050 eq164250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164250 eq165050
  have eq184438 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op y y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq690 y
       have i₂ := eq165058
       grind)
    | exact superpose eq165058 eq690
    | exact resolve eq690 eq165058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq165058
  have eq184488 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184438
       have i₂ := eq164062 y
       grind)
    | exact superpose eq164062 eq184438
    | exact resolve eq184438 eq164062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164062 eq184438
  have eq184489 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq184488
  have eq184526 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq184489
       grind)
    | exact superpose eq184489 eq16
    | exact resolve eq16 eq184489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184489
  have eq184714 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq184526
       have i₂ := eq164102
       grind)
    | exact superpose eq164102 eq184526
    | exact resolve eq184526 eq164102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164102 eq184526
  have eq184715 : False := by grind
  exact eq184715

/-- `Equation3958`: `x ◇ y = (y ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation3958 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3958 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3958.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X2)) X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq53 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 (M.op x y)) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) X3) = (M.op (M.op X3 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq14 X0 X3 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq92 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq117
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq120
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X3 (M.op X1 (M.op X0 X2))) ∨ (M.op X1 (M.op X0 X2)) = X3 ∨ (M.op X1 (M.op X0 X2)) = (k (M.op X1 (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 X2)) X3
       have i₂ := eq57 X0 X1 X2 (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 X2)) X3
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X0 X2)) X0
       have r₂ := eq57 X0 X1 X2 (M.op X1 (M.op X0 X2))
       grind)
    | (have r₁ := eq12 X3 (M.op X1 (M.op X3 X2))
       have r₂ := eq57 X3 X1 X2 X3
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq75
  have eq799 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq782 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq782
    | (have j0 := eq782 X0 x
       grind)
    | exact resolve eq782 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq4676 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq90 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq5770 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq799 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq799
    | (have j0 := eq799 y
       grind)
    | exact resolve eq799 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq5782 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5770
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq5770
    | exact resolve eq5770 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5770
  have eq5801 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5782
    | exact resolve eq5782 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5782
  have eq5810 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5801
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq5801
    | exact resolve eq5801 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5801
  have eq5816 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5810
    | exact resolve eq5810 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5810
  have eq8817 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X0 (M.op X1 X2)) X1) ∨ (M.op X0 (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq530 X1 X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq9327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9327
    | exact resolve eq9327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9327
  have eq9339 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9328
       have r₂ := eq28
       grind)
    | exact resolve eq9328 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9328
  have eq9343 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9339
    | exact resolve eq9339 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9339
  have eq9352 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9343 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9343
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9343
       grind)
    | exact resolve eq12 eq9343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9343
  have eq15523 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9352
    | (have j0 := eq9352 (σ x)
       grind)
    | (have r₁ := eq9352 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq9352 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9352
  have eq15524 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15523
  have eq15525 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15524
  have eq15542 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq15525 eq102
    | exact resolve eq102 eq15525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq15525
  have eq15554 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15542
  have eq15712 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq15554
       grind)
    | exact superpose eq15554 eq93
    | exact resolve eq93 eq15554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15720 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ y = (k y X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq15554
       grind)
    | exact superpose eq15554 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15554
       grind)
    | exact resolve eq12 eq15554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15554
  have eq15748 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15712
    | exact resolve eq15712 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq140158 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15720 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15720
    | (have j0 := eq15720 x
       grind)
    | (have r₁ := eq15720 x
       have r₂ := eq19
       grind)
    | exact resolve eq15720 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15720
  have eq140167 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq140158
  have eq140168 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq140167
  have eq140203 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq140168
       grind)
    | exact superpose eq140168 eq87
    | exact resolve eq87 eq140168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq140168
  have eq140291 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq140203
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq140203
    | exact resolve eq140203 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140203
  have eq141138 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq140291 eq5816
    | exact resolve eq5816 eq140291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5816 eq140291
  have eq141194 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq141138
  have eq141240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq141194 eq15748
    | exact resolve eq15748 eq141194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141194
  have eq141371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq141240
  have eq141392 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq141371
       have r₂ := eq28
       grind)
    | exact resolve eq141371 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141371
  have eq141397 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (σ y)) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq141392 eq54
    | exact resolve eq54 eq141392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq148390 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq141397
    | (have j0 := eq141397 (σ x)
       grind)
    | exact resolve eq141397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141397
  have eq148579 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq141392 eq148390
    | exact resolve eq148390 eq141392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141392 eq148390
  have eq148592 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq148579
  have eq148735 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (M.op (σ x) (σ x))) X1) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq148592 eq57
    | exact resolve eq57 eq148592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148592
  have eq148748 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ y) X1) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq148735 X1 x
       have i₂ := eq57 sF2 X1 sF2 x
       grind)
    | exact superpose eq57 eq148735
    | exact resolve eq148735 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148735
  have eq149285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq148748 eq15748
    | exact resolve eq15748 eq148748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15748 eq148748
  have eq149492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq149285
  have eq149581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq149492
    | exact resolve eq149492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149492
  have eq149601 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq149581
       have r₂ := eq28
       grind)
    | exact resolve eq149581 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149581
  have eq149606 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq149601 eq30
    | exact resolve eq30 eq149601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149601
  have eq149750 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq149606
    | exact resolve eq149606 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149606
  have eq149751 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq149750
  have eq149773 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq149751 eq30
    | exact resolve eq30 eq149751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149789 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq149751 eq127
    | exact resolve eq127 eq149751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq149751
  have eq150184 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq160 eq149789
    | exact resolve eq149789 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149789
  have eq150198 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq149773
    | exact resolve eq149773 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq149773
  have eq150219 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq150198 eq53
    | exact resolve eq53 eq150198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq150234 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq150198 eq121
    | exact resolve eq121 eq150198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq150778 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq150234
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq150234
    | exact resolve eq150234 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150234
  have eq150907 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y y)) X1) = (M.op (M.op x y) X1) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq150184 eq57
    | exact resolve eq57 eq150184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150184
  have eq150939 : ∀ X1 : G, (M.op y X1) = (M.op (M.op x y) X1) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq150907 x X1
       have i₂ := eq57 y x y X1
       grind)
    | exact superpose eq57 eq150907
    | exact resolve eq150907 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150907
  have eq163677 : (M.op x x) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq150219 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq150219
    | (have j0 := eq150219 x
       grind)
    | exact resolve eq150219 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164024 : (M.op x x) = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq163677 eq150939
    | exact resolve eq150939 eq163677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150939 eq163677
  have eq164039 : (M.op x x) = (M.op y x) ∨ x = y := by grind
  clear eq164024
  have eq164047 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq57 y X0 x X1
       have i₂ := eq164039
       grind)
    | exact superpose eq164039 eq57
    | exact resolve eq57 eq164039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164039
  have eq164058 : ∀ X1 : G, (M.op x X1) = (M.op y X1) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq164047 x X1
       have i₂ := eq57 x x x X1
       grind)
    | exact superpose eq57 eq164047
    | exact resolve eq164047 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq164047
  have eq164652 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq164058 y
       grind)
    | exact superpose eq164058 eq93
    | exact resolve eq93 eq164058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164834 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq150219 y
       have i₂ := eq164058 y
       grind)
    | exact superpose eq164058 eq150219
    | exact resolve eq150219 eq164058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150219 eq164058
  have eq164860 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by grind
  clear eq164834
  have eq164996 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq164860
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq164860
    | exact resolve eq164860 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164860
  have eq165028 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq164652
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq164652
    | exact resolve eq164652 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164652
  have eq165048 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq165028
    | exact resolve eq165028 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165028
  have eq165057 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq150198 eq164996
    | exact resolve eq164996 eq150198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150198 eq164996
  have eq165085 : y = (M.op y y) ∨ x = y := by grind
  clear eq165057
  have eq165819 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq165085
       grind)
    | exact superpose eq165085 eq93
    | exact resolve eq93 eq165085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq165085
  have eq166060 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq165819
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq165819
    | exact resolve eq165819 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165819
  have eq166288 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) x) ∨ x = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq8817 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8817
    | (have j0 := eq8817 X0 x y
       grind)
    | exact resolve eq8817 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8817
  have eq166978 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq166060 eq150778
    | exact resolve eq150778 eq166060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150778
  have eq167014 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq166978
  have eq167865 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq167014 eq160
    | exact resolve eq160 eq167014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq167014
  have eq167936 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq167865
    | exact resolve eq167865 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167865
  have eq1320270 : y = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq167936 eq166288
    | exact resolve eq166288 eq167936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166288 eq167936
  have eq1320372 : y = (k y x) ∨ x = y := by grind
  clear eq1320270
  have eq1320558 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4676 x
       have i₂ := eq1320372
       grind)
    | exact superpose eq1320372 eq4676
    | (have j0 := eq4676 x
       grind)
    | exact resolve eq4676 eq1320372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4676 eq1320372
  have eq1320690 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1320558
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1320558
    | exact resolve eq1320558 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320558
  have eq1320753 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1320690
       have r₂ := eq166060
       grind)
    | exact resolve eq1320690 eq166060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166060 eq1320690
  have eq1320802 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1320753
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1320753
    | exact resolve eq1320753 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320753
  have eq1320849 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1320802
    | exact resolve eq1320802 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320802
  have eq1320893 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1320849
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1320849
    | exact resolve eq1320849 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320849
  have eq1327943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1320893 eq165048
    | exact resolve eq165048 eq1320893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165048 eq1320893
  have eq1328165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1327943
  have eq1328265 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1328165
       have r₂ := eq28
       grind)
    | exact resolve eq1328165 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328165
  have eq1328269 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1328265 eq30
    | exact resolve eq30 eq1328265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1328265
  have eq1329827 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1328269
    | exact resolve eq1328269 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1328269
  have eq1329828 : x = y := by grind
  clear eq1329827
  have eq1329855 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1329828
       grind)
    | exact superpose eq1329828 eq19
    | exact resolve eq19 eq1329828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1329856 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1329828
       grind)
    | exact superpose eq1329828 eq25
    | exact resolve eq25 eq1329828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1329828
  have eq1330206 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1329856
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1329856
    | exact resolve eq1329856 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1329856
  have eq1330393 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1330206 eq27
    | exact resolve eq27 eq1330206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1330206
  have eq1331527 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1330393 eq69
    | exact resolve eq69 eq1330393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1330393
  have eq1331621 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1331527
       have i₂ := eq1329855
       grind)
    | exact superpose eq1329855 eq1331527
    | exact resolve eq1331527 eq1329855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329855 eq1331527
  have eq1331644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1331621 eq15
    | exact resolve eq15 eq1331621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331621
  have eq1332357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1331644
    | exact resolve eq1331644 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1331644
  have eq1332513 : False := by grind
  exact eq1332513

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_Equation3997 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X2)) X1) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 X0 X1 X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1 X2
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq104 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq108 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       have j1 := eq56 X1 X0 x
       grind)
    | (have r₁ := eq104 X1 X0
       have r₂ := eq56 X0 X1 X1
       grind)
    | (have r₁ := eq104 X0 X1
       have r₂ := eq56 X0 X1 X0
       grind)
    | exact resolve eq104 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq104
  have eq533 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq108 (σ X1) (σ X0)
       grind)
    | exact superpose eq108 eq15
    | exact resolve eq15 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1
       have i₂ := eq108 X1 X0
       grind)
    | exact superpose eq108 eq533
    | exact resolve eq533 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq533
  have eq543 : False := by grind
  exact eq543

/-- `Equation4001`: `x ◇ y = (z ◇ (x ◇ w)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation4001 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4001 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4001.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X3)) X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq53 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 (M.op x y)) X0) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X3 (M.op X1 (M.op X0 X2))) ∨ (M.op X1 (M.op X0 X2)) = X3 ∨ (M.op X1 (M.op X0 X2)) = (k (M.op X1 (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 X2)) X3
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X2)) X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 X2)) X3
       grind)
    | (have r₁ := eq12 X1 (M.op X2 (M.op X1 X3))
       have r₂ := eq14 X1 X1 X2 X3
       grind)
    | (have r₁ := eq12 (M.op X2 (M.op X0 X3)) X0
       have r₂ := eq14 X0 (M.op X2 (M.op X0 X3)) X2 X3
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq89 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq89
  have eq94 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq118 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq121 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq118
  have eq122 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq121
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq16
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq122 eq16
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq76
  have eq710 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq653 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq653
    | (have j0 := eq653 X0 x
       grind)
    | exact resolve eq653 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq653 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq838 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X0 (M.op X1 X2)) X1) ∨ (M.op X0 (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq70 X1 X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq3551 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) x) ∨ x = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq838 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq838
    | (have j0 := eq838 X0 x y
       grind)
    | exact resolve eq838 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq4955 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq710 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq710
    | (have j0 := eq710 y
       grind)
    | exact resolve eq710 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq4967 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4955
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq4955
    | exact resolve eq4955 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4955
  have eq4986 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq4967
    | exact resolve eq4967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4967
  have eq4995 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4986
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq4986
    | exact resolve eq4986 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4986
  have eq5001 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq4995
    | exact resolve eq4995 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4995
  have eq10003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10003
    | exact resolve eq10003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10003
  have eq10015 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq10004
       have r₂ := eq28
       grind)
    | exact resolve eq10004 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10004
  have eq10019 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10015
    | exact resolve eq10015 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10015
  have eq10028 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10019 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10019
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10019
       grind)
    | exact resolve eq12 eq10019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10019
  have eq15909 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10028
    | (have j0 := eq10028 (σ x)
       grind)
    | (have r₁ := eq10028 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq10028 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10028
  have eq15910 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15909
  have eq15911 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15910
  have eq15926 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq15911 eq103
    | exact resolve eq103 eq15911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq15911
  have eq15939 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15926
  have eq15954 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq15939
       grind)
    | exact superpose eq15939 eq94
    | exact resolve eq94 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15961 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ y = (k y X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq15939
       grind)
    | exact superpose eq15939 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15939
       grind)
    | exact resolve eq12 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15939
  have eq15986 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15954
    | exact resolve eq15954 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15954
  have eq133263 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15961 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15961
    | (have j0 := eq15961 x
       grind)
    | (have r₁ := eq15961 x
       have r₂ := eq19
       grind)
    | exact resolve eq15961 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961
  have eq133272 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq133263
  have eq133273 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq133272
  have eq134241 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq133273
       grind)
    | exact superpose eq133273 eq88
    | exact resolve eq88 eq133273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq133273
  have eq134331 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq134241
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq134241
    | exact resolve eq134241 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134241
  have eq134383 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq134331 eq5001
    | exact resolve eq5001 eq134331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5001 eq134331
  have eq134440 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq134383
  have eq134485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq134440 eq15986
    | exact resolve eq15986 eq134440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134440
  have eq134613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq134485
  have eq134631 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq134613
       have r₂ := eq28
       grind)
    | exact resolve eq134613 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134613
  have eq135568 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (σ y)) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq134631 eq54
    | exact resolve eq54 eq134631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq141314 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq27 eq135568
    | (have j0 := eq135568 X0 (σ x)
       grind)
    | exact resolve eq135568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135568
  have eq141487 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq134631 eq141314
    | exact resolve eq141314 eq134631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134631 eq141314
  have eq141598 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq141487 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141487
  have eq142753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq141598 eq15986
    | exact resolve eq15986 eq141598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15986 eq141598
  have eq142964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq142753
  have eq143047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq142964
    | exact resolve eq142964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142964
  have eq143067 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq143047
       have r₂ := eq28
       grind)
    | exact resolve eq143047 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143047
  have eq144028 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq143067 eq30
    | exact resolve eq30 eq143067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143067
  have eq144172 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq144028
    | exact resolve eq144028 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144028
  have eq144173 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq144172
  have eq144194 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq144173 eq30
    | exact resolve eq30 eq144173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144210 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq144173 eq128
    | exact resolve eq128 eq144173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq144173
  have eq144598 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq161 eq144210
    | exact resolve eq144210 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144210
  have eq144612 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq144194
    | exact resolve eq144194 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144194
  have eq144633 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 y) X0) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq144612 eq53
    | exact resolve eq53 eq144612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq144648 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq144612 eq122
    | exact resolve eq122 eq144612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq145182 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq144648
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq144648
    | exact resolve eq144648 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144648
  have eq146889 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 (M.op y y)) X0) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq144598 eq14
    | exact resolve eq14 eq144598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146921 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq146889 X0 x
       have i₂ := eq14 y X0 x y
       grind)
    | exact superpose eq14 eq146889
    | exact resolve eq146889 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146889
  have eq159943 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq144633 X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq144633
    | (have j0 := eq144633 X0 x
       grind)
    | exact resolve eq144633 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144633
  have eq160117 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq159943 eq146921
    | exact resolve eq146921 eq159943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146921
  have eq160154 : (M.op y y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq159943 eq144598
    | exact resolve eq144598 eq159943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144598 eq159943
  have eq160246 : (M.op y y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq160154
  have eq160269 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq160117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160117
  have eq160520 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq160269 y
       grind)
    | exact superpose eq160269 eq94
    | exact resolve eq94 eq160269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160269
  have eq160892 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq160520
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq160520
    | exact resolve eq160520 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160520
  have eq160912 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq160892
    | exact resolve eq160892 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160892
  have eq161015 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq160912 eq145182
    | exact resolve eq145182 eq160912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145182
  have eq161043 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq161015
  have eq161196 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq161043 eq161
    | exact resolve eq161 eq161043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq161043
  have eq161279 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq161196
    | exact resolve eq161196 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq161196
  have eq162822 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq144612 eq161279
    | exact resolve eq161279 eq144612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144612 eq161279
  have eq162924 : y = (M.op y y) ∨ x = y := by grind
  clear eq162822
  have eq163813 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq162924
       grind)
    | exact superpose eq162924 eq94
    | exact resolve eq94 eq162924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163904 : y = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq160246
       have i₂ := eq162924
       grind)
    | exact superpose eq162924 eq160246
    | exact resolve eq160246 eq162924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160246 eq162924
  have eq163935 : y = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq163904
  have eq164048 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq163813
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq163813
    | exact resolve eq163813 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163813
  have eq164070 : y = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq163935 eq3551
    | exact resolve eq3551 eq163935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3551 eq163935
  have eq164079 : y = (k y x) ∨ x = y := by grind
  clear eq164070
  have eq164397 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq735 x y
       have i₂ := eq164079
       grind)
    | exact superpose eq164079 eq735
    | (have j0 := eq735 x y
       grind)
    | exact resolve eq735 eq164079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq164079
  have eq164432 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq164397
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq164397
    | exact resolve eq164397 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164397
  have eq164450 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq164432
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq164432
    | exact resolve eq164432 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164432
  have eq164456 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq164450
       have r₂ := eq164048
       grind)
    | exact resolve eq164450 eq164048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164048 eq164450
  have eq164460 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq164456
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq164456
    | exact resolve eq164456 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq164456
  have eq164464 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq164460
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq164460
    | exact resolve eq164460 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164460
  have eq164468 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq164464
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164464
    | exact resolve eq164464 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164464
  have eq164472 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq164468
    | exact resolve eq164468 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164468
  have eq164476 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq164472
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq164472
    | exact resolve eq164472 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164472
  have eq164480 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq164476
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164476
    | exact resolve eq164476 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164476
  have eq171500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq164480 eq160912
    | exact resolve eq160912 eq164480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160912 eq164480
  have eq171530 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq171500
  have eq171607 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq171530
       have r₂ := eq28
       grind)
    | exact resolve eq171530 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171530
  have eq171613 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq171607 eq30
    | exact resolve eq30 eq171607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq171607
  have eq171805 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq171613
    | exact resolve eq171613 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq171613
  have eq171806 : x = y := by grind
  clear eq171805
  have eq171825 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq171806
       grind)
    | exact superpose eq171806 eq19
    | exact resolve eq19 eq171806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq171826 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq171806
       grind)
    | exact superpose eq171806 eq25
    | exact resolve eq25 eq171806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq171806
  have eq172099 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq171826
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq171826
    | exact resolve eq171826 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq171826
  have eq172272 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq172099 eq27
    | exact resolve eq27 eq172099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq172099
  have eq172542 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq172272 eq69
    | exact resolve eq69 eq172272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq172272
  have eq172578 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq172542
       have i₂ := eq171825
       grind)
    | exact superpose eq171825 eq172542
    | exact resolve eq172542 eq171825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171825 eq172542
  have eq173623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172578 eq15
    | exact resolve eq15 eq172578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172578
  have eq173953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq173623
    | exact resolve eq173623 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq173623
  have eq174054 : False := by grind
  exact eq174054

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_x_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  clear eq24
  have eq54 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq102 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq96 y x
       grind)
    | exact superpose eq96 eq102
    | (have j1 := eq96 y x
       grind)
    | exact resolve eq102 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq136 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq134
    | exact resolve eq134 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq137 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq136
    | exact resolve eq136 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq137 eq96
    | (have j0 := eq96 (σ y) (σ x)
       grind)
    | exact resolve eq96 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq206
    | exact resolve eq206 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq210 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq207
       have r₂ := eq27
       grind)
    | exact resolve eq207 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq212 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq210
    | exact resolve eq210 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq274 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq212 eq55
    | exact resolve eq55 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq283 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq274
    | (have j0 := eq274 X0
       grind)
    | exact resolve eq274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq285 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq212 eq283
    | exact resolve eq283 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq283
  have eq291 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq295 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq291
    | (have j0 := eq291 (σ y)
       grind)
    | exact resolve eq291 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq295 eq291
    | exact resolve eq291 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq343 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq353 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq343 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq343 (σ x)
       grind)
    | exact resolve eq13 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq359 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq353 X0
       grind)
    | (have r₁ := eq353 X0
       have r₂ := eq295
       grind)
    | exact resolve eq353 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq353
  have eq401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq359 eq137
    | exact resolve eq137 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq359
  have eq406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq401
  have eq408 : x = (M.op x y) := by
    first
    | (have r₁ := eq406
       have r₂ := eq27
       grind)
    | exact resolve eq406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq411 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq408 eq20
    | exact resolve eq20 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq413 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq408 eq54
    | exact resolve eq54 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq422 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq413 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq413
    | (have j0 := eq413 X0
       grind)
    | exact resolve eq413 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq424 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq411
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq411
    | exact resolve eq411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq426 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq408 eq422
    | exact resolve eq422 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq428 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq408 eq70
    | exact resolve eq70 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq429 : x ≠ (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq408 eq428
    | exact resolve eq428 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq430 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq424 eq26
    | exact resolve eq26 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq476 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq426 y
       grind)
    | exact superpose eq426 eq18
    | (have j1 := eq426 y
       grind)
    | exact resolve eq18 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq426
  have eq481 : x = (M.op x x) := by
    first
    | exact superpose eq408 eq476
    | exact resolve eq476 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq476
  have eq487 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq429
       have i₂ := eq481
       grind)
    | exact superpose eq481 eq429
    | (have r₁ := eq429
       have r₂ := eq481
       grind)
    | exact resolve eq429 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq481
  have eq493 : x = (k y x) := by grind
  clear eq487
  have eq556 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq493
       grind)
    | exact superpose eq493 eq102
    | exact resolve eq102 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq493
  have eq562 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq424 eq556
    | exact resolve eq556 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq563 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq562
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq562
    | exact resolve eq562 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq562
  have eq564 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq424 eq563
    | exact resolve eq563 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq563
  have eq683 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq564 eq96
    | (have j0 := eq96 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq564
  have eq684 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq683
  have eq686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq430 eq684
    | exact resolve eq684 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq684
  have eq689 : False := by grind
  exact eq689

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_y_x_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  clear eq24
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
  clear eq39
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
  have eq178 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1056 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1086 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1093 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1060 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1110 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1093 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq1093 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq1093 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1093 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1131 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1110 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1110
    | (have j0 := eq1110 (σ X0) X1
       grind)
    | exact resolve eq1110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1134 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1055
       grind)
    | exact superpose eq1055 eq40
    | exact resolve eq40 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1055
  have eq1135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1134
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1134
    | exact resolve eq1134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1137 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1135
    | exact resolve eq1135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1137 eq1056
    | exact resolve eq1056 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq1137
  have eq1181 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1174
       have r₂ := eq27
       grind)
    | exact resolve eq1174 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1191 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1181 eq180
    | exact resolve eq180 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1181 eq1191
    | exact resolve eq1191 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq1191
  have eq1215 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1195 eq26
    | (have j1 := eq1195 (σ y)
       grind)
    | exact resolve eq26 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1226 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1215
  have eq1237 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq180 x x x
       have i₂ := eq1226
       grind)
    | exact superpose eq1226 eq180
    | exact resolve eq180 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1241 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1226 eq1237
    | exact resolve eq1237 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq1237
  have eq1278 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1241 y
       grind)
    | exact superpose eq1241 eq18
    | (have j1 := eq1241 y
       grind)
    | exact resolve eq18 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1289 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1278
  have eq1295 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1289 eq179
    | exact resolve eq179 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1377 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1295
    | (have j0 := eq1295 (σ y) X0
       grind)
    | exact resolve eq1295 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1414 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1289 eq1377
    | exact resolve eq1377 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1439 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1414 eq26
    | (have j1 := eq1414 (σ y)
       grind)
    | exact resolve eq26 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1459 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1289 eq1439
    | exact resolve eq1439 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289 eq1439
  have eq1476 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1459 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq1459
       grind)
    | exact resolve eq13 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1479 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1476 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1514 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1479 eq141
    | exact resolve eq141 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1479
  have eq1522 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1514
    | exact resolve eq1514 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1514
  have eq1574 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1086 x
       have i₂ := eq1522
       grind)
    | exact superpose eq1522 eq1086
    | (have j0 := eq1086 x
       grind)
    | (have r₁ := eq1086 x
       have r₂ := eq1522
       grind)
    | exact resolve eq1086 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1575 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1574
  have eq1912 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq180 x x x
       have i₂ := eq1575
       grind)
    | exact superpose eq1575 eq180
    | exact resolve eq180 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1916 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1575 eq1912
    | exact resolve eq1912 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq1912
  have eq1926 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1916 y
       grind)
    | exact superpose eq1916 eq18
    | (have j1 := eq1916 y
       grind)
    | exact resolve eq18 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916
  have eq1940 : x = (M.op x y) := by grind
  clear eq1926
  have eq1947 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1940
       grind)
    | exact superpose eq1940 eq18
    | exact resolve eq18 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1948 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1940
       grind)
    | exact superpose eq1940 eq22
    | exact resolve eq22 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1958 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1948 eq20
    | exact resolve eq20 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq2061 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1947 eq178
    | exact resolve eq178 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2073 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2061 X0
       have i₂ := eq1940
       grind)
    | exact superpose eq1940 eq2061
    | exact resolve eq2061 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940 eq2061
  have eq2082 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2073 eq1947
    | exact resolve eq1947 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947 eq2073
  have eq2117 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2082 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq2082
       grind)
    | exact resolve eq13 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq2123 : ∀ X0 : G, (k (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117
  have eq2173 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2123 eq1131
    | (have j0 := eq1131 (M.op x y) X0
       grind)
    | exact resolve eq1131 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq2123
  have eq2186 : ∀ X0 : G, (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2173 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2195 : ∀ X0 : G, (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq2186
    | (have j0 := eq2186 X0
       grind)
    | exact resolve eq2186 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2186
  have eq2202 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1958 eq2195
    | exact resolve eq2195 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2227 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2202 eq1086
    | (have j0 := eq1086 (σ x)
       grind)
    | (have r₁ := eq1086 (σ x)
       have r₂ := eq2202 (σ x)
       grind)
    | exact resolve eq1086 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq2202
  have eq2236 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2227
  have eq2305 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq2236 eq180
    | exact resolve eq180 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq2309 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq2236 eq2305
    | exact resolve eq2305 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236 eq2305
  have eq2321 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2309 eq26
    | (have j1 := eq2309 (σ y)
       grind)
    | exact resolve eq26 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2309
  have eq2347 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2321 eq27
    | exact resolve eq27 eq2321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2321
  have eq2349 : False := by grind
  exact eq2349

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_x_y_pyy_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
  clear eq24 eq35
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
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op (M.op X0 X1) X2) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq216 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : ∀ X2 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x x) X2) = X2 := by
    intro X2
    first
    | exact superpose eq60 eq66
    | (have j0 := eq66 x y (M.op x y) x
       grind)
    | exact resolve eq66 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1689 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1691 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq6063 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1691 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1691
    | (have j0 := eq1691 (τ X0)
       grind)
    | exact resolve eq1691 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6071 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6063 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6063
    | (have j0 := eq6063 X0
       grind)
    | exact resolve eq6063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6063
  have eq6077 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6071 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6071
    | (have j0 := eq6071 X0
       grind)
    | exact resolve eq6071 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6071
  have eq8002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq8003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8002
    | exact resolve eq8002 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8002
  have eq8014 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8003
       have r₂ := eq27
       grind)
    | exact resolve eq8003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8003
  have eq8016 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8014
    | exact resolve eq8014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8014
  have eq8020 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8016 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq8016
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8016
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8016
       grind)
    | exact resolve eq13 eq8016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8016
  have eq8044 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq8020
  have eq8070 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8044 eq49
    | exact resolve eq49 eq8044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8044
  have eq8092 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq8070
    | exact resolve eq8070 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8070
  have eq8095 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq6077 x
       grind)
    | (have r₁ := eq8092
       have r₂ := eq6077 x
       grind)
    | exact resolve eq8092 eq6077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6077 eq8092
  have eq8096 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq216
    | exact resolve eq216 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8098 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq8095
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8095
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8095
       grind)
    | exact resolve eq13 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8102 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X2 X3 x x
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq57
    | exact resolve eq57 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8095
  have eq8122 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8098
  have eq8133 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X3
    first
    | (have i₁ := eq8102 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq8102
    | exact resolve eq8102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8102
  have eq8141 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8133 x
       have i₂ := eq216 x
       grind)
    | exact superpose eq216 eq8133
    | exact resolve eq8133 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8133
  have eq8147 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq8122
       grind)
    | exact superpose eq8122 eq43
    | exact resolve eq43 eq8122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq8122
  have eq8171 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8147
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8147
    | exact resolve eq8147 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8147
  have eq13325 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8096 eq8141
    | exact resolve eq8141 eq8096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8096 eq8141
  have eq13380 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13325
  have eq13470 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13380 y
       grind)
    | exact superpose eq13380 eq18
    | (have j1 := eq13380 y
       grind)
    | exact resolve eq18 eq13380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13380
  have eq13506 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13470
  have eq13537 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13506 eq61
    | exact resolve eq61 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq15181 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq13537
    | (have j0 := eq13537 (σ y) X0
       grind)
    | exact resolve eq13537 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13537
  have eq15335 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13506 eq15181
    | exact resolve eq15181 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13506 eq15181
  have eq15402 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15335
  have eq15451 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15402
    | (have j0 := eq15402 (σ y)
       grind)
    | exact resolve eq15402 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15402
  have eq15584 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15451 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15451
       grind)
    | exact resolve eq13 eq15451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15451
  have eq15650 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15584
       have r₂ := eq8171
       grind)
    | exact resolve eq15584 eq8171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171 eq15584
  have eq15922 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15650 eq49
    | exact resolve eq49 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq15650
  have eq15946 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq15922
    | exact resolve eq15922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15922
  have eq16208 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq15946
       grind)
    | exact superpose eq15946 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15946
  have eq16209 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq16208
  have eq17194 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq16209
       grind)
    | exact superpose eq16209 eq216
    | exact resolve eq216 eq16209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17200 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X2 X3 x x
       have i₂ := eq16209
       grind)
    | exact superpose eq16209 eq57
    | exact resolve eq57 eq16209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq16209
  have eq17235 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) := by
    intro X3
    first
    | (have i₁ := eq17200 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq17200
    | exact resolve eq17200 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17200
  have eq17243 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17235 x
       have i₂ := eq216 x
       grind)
    | exact superpose eq216 eq17235
    | exact resolve eq17235 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq17235
  have eq27543 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17194 eq17243
    | exact resolve eq17243 eq17194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17194 eq17243
  have eq27619 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27543 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27543
  have eq28207 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27619 y
       grind)
    | exact superpose eq27619 eq18
    | (have j1 := eq27619 y
       grind)
    | exact resolve eq18 eq27619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27619
  have eq28260 : x = (M.op x y) := by grind
  clear eq28207
  have eq28307 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28260 eq20
    | exact resolve eq20 eq28260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28310 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq28260 eq60
    | exact resolve eq60 eq28260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq28361 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq28260 eq1215
    | (have j0 := eq1215 X0
       grind)
    | exact resolve eq1215 eq28260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq28365 : ∀ X0 : G, (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28361 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28361
  have eq28417 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28307
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28307
    | exact resolve eq28307 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28307
  have eq28432 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq28417 eq26
    | exact resolve eq26 eq28417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq34979 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq28310 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28310
    | (have j0 := eq28310 y X0
       grind)
    | exact resolve eq28310 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28310
  have eq35164 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq28260 eq34979
    | exact resolve eq34979 eq28260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34979
  have eq35311 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35164 y
       grind)
    | exact superpose eq35164 eq18
    | (have j1 := eq35164 y
       grind)
    | exact resolve eq18 eq35164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35164
  have eq35355 : x = (M.op x x) := by
    first
    | exact superpose eq28260 eq35311
    | exact resolve eq35311 eq28260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28260 eq35311
  have eq35417 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28365 X0
       have i₂ := eq35355
       grind)
    | exact superpose eq35355 eq28365
    | exact resolve eq28365 eq35355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28365 eq35355
  have eq35670 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1691 x
       have i₂ := eq35417 x
       grind)
    | exact superpose eq35417 eq1691
    | (have j0 := eq1691 x
       grind)
    | exact resolve eq1691 eq35417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691 eq35417
  have eq35745 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq35670
  have eq35798 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35745
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35745
    | exact resolve eq35745 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35745
  have eq35841 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28417 eq35798
    | exact resolve eq35798 eq28417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28417 eq35798
  have eq39448 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq35841 eq62
    | exact resolve eq62 eq35841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq39505 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq35841 eq39448
    | exact resolve eq39448 eq35841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35841 eq39448
  have eq39542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39505 eq28432
    | exact resolve eq28432 eq39505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28432 eq39505
  have eq39626 : False := by grind
  exact eq39626
