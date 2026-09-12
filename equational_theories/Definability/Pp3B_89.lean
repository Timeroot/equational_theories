import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pyx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq118 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq74
    | exact resolve eq74 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq88
    | exact resolve eq88 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq166 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq129 X0 X0 X0
       grind)
    | exact superpose eq129 eq129
    | exact resolve eq129 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq133 X2 X3 X4
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq133
    | exact resolve eq133 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq130 X2 X3
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq130
    | exact resolve eq130 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq67
    | exact resolve eq67 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq208 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq129 X2 X3 X2
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq129
    | exact resolve eq129 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X2 X2
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq88
    | exact resolve eq88 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq215 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq133 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq133 eq9
    | exact resolve eq9 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq129 X3 x X0
       grind)
    | exact superpose eq129 eq206
    | exact resolve eq206 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq890 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70 X2 X2 X3 X4
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq70
    | exact resolve eq70 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 (M.op X1 X0) X2 X3
       have i₂ := eq133 X0 X0 X1
       grind)
    | exact superpose eq133 eq70
    | exact resolve eq70 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq70 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq892 X0 X1 x x
       have i₂ := eq70 X0 X0 x x
       grind)
    | exact superpose eq70 eq892
    | exact resolve eq892 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq1104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  have eq1207 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X3 X3)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq118 X2 X3
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq118
    | exact resolve eq118 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1287 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133 X1 (M.op X2 X0) (M.op X2 (M.op X2 X2))
       have i₂ := eq118 X0 X2
       grind)
    | exact superpose eq118 eq133
    | exact resolve eq133 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 (M.op X3 X0) (M.op X3 (M.op X3 X3)) X2 X1
       have i₂ := eq118 X0 X3
       grind)
    | exact superpose eq118 eq206
    | exact resolve eq206 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1843 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq166 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq206 X1 X2 X0 X4
       grind)
    | exact superpose eq206 eq166
    | exact resolve eq166 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1879 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq166 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq166 eq9
    | exact resolve eq9 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1992 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1843 X0 X1 X2 X3 X4
       have i₂ := eq63 X4 X0
       grind)
    | exact superpose eq63 eq1843
    | exact resolve eq1843 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq2040 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1992 X0 X1 X2 X3 X4
       have i₂ := eq63 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq63 eq1992
    | exact resolve eq1992 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq2063 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2040 X0 X1 X2 X3 X4
       have i₂ := eq206 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq206 eq2040
    | exact resolve eq2040 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2068 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2063 X0 x x X3 X4
       have i₂ := eq210 x x X0
       grind)
    | exact superpose eq210 eq2063
    | exact resolve eq2063 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq2063
  have eq2087 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2068 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq166 X0 x X1
       grind)
    | exact superpose eq166 eq2068
    | exact resolve eq2068 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2155 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2087 X0 X1 X2
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq2087
    | exact resolve eq2087 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2171 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2155 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq2155
    | exact resolve eq2155 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2155
  have eq3212 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq208 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq207 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq207 eq208
    | exact resolve eq208 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3340 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3212 X0 X1 X2 X3
       have i₂ := eq2171 X0 (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq2171 eq3212
    | exact resolve eq3212 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq3396 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3340 X0 x X2 X3
       have i₂ := eq2068 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq2068 eq3340
    | exact resolve eq3340 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068 eq3340
  have eq4112 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq129 X1 x X0
       grind)
    | exact superpose eq129 eq215
    | exact resolve eq215 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq4132 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op X0 (M.op X3 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq215 X3 X2 (M.op X1 (M.op X2 X3)) X0
       have i₂ := eq133 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq133 eq215
    | exact resolve eq215 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq4238 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4112 X0 X1
       have i₂ := eq2171 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2171 eq4112
    | exact resolve eq4112 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112
  have eq4279 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4238 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq166 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq166 eq4238
    | exact resolve eq4238 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq4370 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq4238 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq4238 eq206
    | exact resolve eq206 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4396 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4370 X0 X1 X2
       have i₂ := eq2171 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2171 eq4370
    | exact resolve eq4370 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4370
  have eq4439 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4279 X0 X1
       have i₂ := eq2171 X0 X1 X1
       grind)
    | exact superpose eq2171 eq4279
    | exact resolve eq4279 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq4477 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4439 X0 X1
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq4439
    | exact resolve eq4439 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq4439
  have eq4550 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4477 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq206 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq206 eq4477
    | exact resolve eq4477 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4557 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4238 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq4477 X0 X1
       grind)
    | exact superpose eq4477 eq4238
    | exact resolve eq4238 eq4477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4637 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4557 X0 X1
       have i₂ := eq2171 (M.op X1 X0) X0 X0
       grind)
    | exact superpose eq2171 eq4557
    | exact resolve eq4557 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq4675 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4637 X0 X1
       have i₂ := eq3396 X0 X0 X1
       grind)
    | exact superpose eq3396 eq4637
    | exact resolve eq4637 eq3396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396 eq4637
  have eq4739 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4550 X2 X1 X0
       have i₂ := eq4550 X2 X1 X3
       grind)
    | (have i₁ := eq4550 X0 X1 X2
       have i₂ := eq4550 X0 X1 X1
       grind)
    | exact superpose eq4550 eq4550
    | exact resolve eq4550 eq4550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4744 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4550 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq4477 X0 X2
       grind)
    | exact superpose eq4477 eq4550
    | exact resolve eq4550 eq4477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4477
  have eq4883 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4238 X2 X1
       have i₂ := eq4550 X2 X1 X0
       grind)
    | (have i₁ := eq4238 X0 X1
       have i₂ := eq4550 X0 X1 X1
       grind)
    | exact superpose eq4550 eq4238
    | exact resolve eq4238 eq4550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238 eq4550
  have eq5898 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq4396 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq4396 eq70
    | exact resolve eq70 eq4396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396
  have eq5925 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5898 X0 X1 X2 X3
       have i₂ := eq2171 X3 X2 X2
       grind)
    | exact superpose eq2171 eq5898
    | exact resolve eq5898 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq8798 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1104 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq1104
    | (have j0 := eq1104 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq1104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq8933 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq319 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq208 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq208 eq319
    | exact resolve eq319 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq319
  have eq9166 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8933 X0 X1 X2 X3 X4
       have i₂ := eq2171 X1 X0 X0
       grind)
    | exact superpose eq2171 eq8933
    | exact resolve eq8933 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8933
  have eq9214 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9166 X0 X1 X2 X3 X4
       have i₂ := eq5925 X3 X1 X0 X1
       grind)
    | exact superpose eq5925 eq9166
    | exact resolve eq9166 eq5925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5925 eq9166
  have eq12355 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4744 (M.op X4 X0) X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq9214 X3 X4 X4 X0 X2
       grind)
    | exact superpose eq9214 eq4744
    | exact resolve eq4744 eq9214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4744 eq9214
  have eq14349 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4675 X1 X2
       have i₂ := eq4739 X2 X1 (M.op X1 (M.op X2 X1)) X0
       grind)
    | (have i₁ := eq4675 X1 X2
       have i₂ := eq4739 X0 X1 (M.op X1 (M.op X2 X1)) X2
       grind)
    | exact superpose eq4739 eq4675
    | exact resolve eq4675 eq4739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675 eq4739
  have eq14872 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (τ X2) = (M.op (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))) (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1124 X0 (M.op (M.op X3 (τ X0)) (M.op X0 (M.op X1 X0)))
       have i₂ := eq70 X0 X1 (τ X0) X3
       grind)
    | exact superpose eq70 eq1124
    | (have j0 := eq1124 X2 (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq1124 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq14907 : ∀ X0 X1 X2 X3 : G, (τ X2) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14872 X0 X1 X2 X3
       have i₂ := eq2171 (M.op X1 (M.op X0 X1)) (M.op X3 (τ X2)) (M.op X3 (τ X2))
       grind)
    | exact superpose eq2171 eq14872
    | (have j0 := eq14872 X0 X1 X2 X3
       grind)
    | exact resolve eq14872 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14872
  have eq14920 : ∀ X0 X1 X2 X3 : G, (τ X2) = (M.op (τ X2) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14907 X0 X1 X2 X3
       have i₂ := eq4883 X3 (τ X2) (M.op X1 (M.op X0 X1))
       grind)
    | exact superpose eq4883 eq14907
    | (have j0 := eq14907 X0 X1 X2 X3
       grind)
    | exact resolve eq14907 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907
  have eq14925 : ∀ X0 X1 X2 X3 : G, (τ X2) = (M.op (τ X2) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14920 X0 X1 X2 X3
       have i₂ := eq2171 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq2171 eq14920
    | (have j0 := eq14920 X0 X1 X2 X3
       grind)
    | exact resolve eq14920 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14920
  have eq24746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8798 x y
       grind)
    | exact superpose eq8798 eq16
    | (have j1 := eq8798 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq8798 x y
       grind)
    | exact resolve eq16 eq8798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8798
  have eq24846 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq24746
  have eq29426 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14349 X1 X0 X1
       have i₂ := eq899 X0 X1 X0
       grind)
    | exact superpose eq899 eq14349
    | exact resolve eq14349 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14349
  have eq32041 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq890 x x (M.op X1 (M.op X0 X1)) X2 X3
       have i₂ := eq70 X1 X0 x x
       grind)
    | exact superpose eq70 eq890
    | exact resolve eq890 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32089 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq890 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq192 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq890 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq192 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq192 eq890
    | exact resolve eq890 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq32589 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq32089 X0 X1 x x x X5 X6
       have i₂ := eq12355 X6 x x x X5
       grind)
    | exact superpose eq12355 eq32089
    | exact resolve eq32089 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32089
  have eq32623 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32041 X0 X1 X2 X3
       have i₂ := eq2171 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq2171 eq32041
    | exact resolve eq32041 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32041
  have eq32776 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32623 X0 X1 X2 X3
       have i₂ := eq899 X1 X0 X1
       grind)
    | exact superpose eq899 eq32623
    | exact resolve eq32623 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq32623
  have eq34188 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq890 (M.op X2 (M.op X3 X4)) X1 X5 X4 X3
       have i₂ := eq1207 (M.op X3 X4) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5) X0
       grind)
    | exact superpose eq1207 eq890
    | exact resolve eq890 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq34489 : ∀ X0 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X4 X5)))) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq34188 X0 x x x X4 X5
       have i₂ := eq12355 X5 x x x X4
       grind)
    | exact superpose eq12355 eq34188
    | exact resolve eq34188 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34188
  have eq36585 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (M.op (M.op X1 (M.op X1 X1)) X0) X1 x
       have i₂ := eq1287 X1 X0 x
       grind)
    | exact superpose eq1287 eq133
    | exact resolve eq133 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq36843 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36585 X0 X1
       have i₂ := eq4883 (M.op X1 (M.op X1 X1)) X0 (M.op (M.op X1 (M.op X1 X1)) X0)
       grind)
    | exact superpose eq4883 eq36585
    | exact resolve eq36585 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36585
  have eq37108 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36843 X0 X1
       have i₂ := eq2171 X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2171 eq36843
    | exact resolve eq36843 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36843
  have eq37226 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37108 X0 X1
       have i₂ := eq4883 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq4883 eq37108
    | exact resolve eq37108 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37108
  have eq44051 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X3 X1) (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1288 X1 X2 X0 X3
       have i₂ := eq4132 X0 X1 X1 X1
       grind)
    | exact superpose eq4132 eq1288
    | exact resolve eq1288 eq4132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq4132
  have eq51179 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X4) = (M.op X4 (M.op (M.op X5 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))))) (M.op X2 (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1879 X5 X2 X3 X4
       have i₂ := eq34489 X1 X0 X2
       grind)
    | exact superpose eq34489 eq1879
    | exact resolve eq1879 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879 eq34489
  have eq51796 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X4 (M.op (M.op X1 (M.op X0 X2)) (M.op X2 (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51179 X0 X1 X2 X3 X4 x
       have i₂ := eq12355 (M.op X2 (M.op X3 X4)) x X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq12355 eq51179
    | exact resolve eq51179 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51179
  have eq52581 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1287 X1 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) X2
       have i₂ := eq37226 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq37226 eq1287
    | exact resolve eq1287 eq37226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq37226
  have eq52622 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52581 X0 X1 X2
       have i₂ := eq4883 X1 (M.op X1 X1) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq4883 eq52581
    | exact resolve eq52581 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52581
  have eq52832 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52622 X0 X1 X2
       have i₂ := eq70 X1 X1 (M.op X1 X1) X1
       grind)
    | exact superpose eq70 eq52622
    | exact resolve eq52622 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52622
  have eq52944 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52832 X0 X1 X2
       have i₂ := eq4883 (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))
       grind)
    | exact superpose eq4883 eq52832
    | exact resolve eq52832 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52832
  have eq52997 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52944 X0 X1 X2
       have i₂ := eq32776 (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op X0 X0)
       grind)
    | exact superpose eq32776 eq52944
    | exact resolve eq52944 eq32776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32776 eq52944
  have eq53024 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52997 X0 X1 X2
       have i₂ := eq12355 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))) (M.op X1 (M.op X1 X1)) X1 X1 X1
       grind)
    | exact superpose eq12355 eq52997
    | exact resolve eq52997 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52997
  have eq53043 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53024 X0 X1 X2
       have i₂ := eq4883 X0 X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))
       grind)
    | exact superpose eq4883 eq53024
    | exact resolve eq53024 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53024
  have eq53053 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53043 X0 X1 X2
       have i₂ := eq2171 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2171 eq53043
    | exact resolve eq53043 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53043
  have eq53058 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53053 X0 X1 X2
       have i₂ := eq4883 X1 (M.op X1 X1) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq4883 eq53053
    | exact resolve eq53053 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53053
  have eq53062 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53058 X0 X1 X2
       have i₂ := eq70 X1 X1 (M.op X1 X1) X1
       grind)
    | exact superpose eq70 eq53058
    | exact resolve eq53058 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53058
  have eq104090 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53062 X5 (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) X1
       have i₂ := eq890 X3 X4 X0 X1 X2
       grind)
    | exact superpose eq890 eq53062
    | exact resolve eq53062 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq53062
  have eq104741 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104090 X0 X1 X2 X3 X4 X5
       have i₂ := eq2171 (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X2 X1) (M.op X2 X1)
       grind)
    | exact superpose eq2171 eq104090
    | exact resolve eq104090 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104090
  have eq104892 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104741 X0 X1 X0 X3 X4 X5
       have i₂ := eq4883 X0 X1 (M.op X3 (M.op (M.op X4 X3) X0))
       grind)
    | exact superpose eq4883 eq104741
    | exact resolve eq104741 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104741
  have eq104969 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 (M.op (M.op (M.op X4 X3) X0) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 (M.op (M.op (M.op X4 X3) X0) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104892 X0 X1 X2 X1 X4 X5
       have i₂ := eq2171 (M.op (M.op X4 X1) X0) X1 X1
       grind)
    | exact superpose eq2171 eq104892
    | exact resolve eq104892 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104892
  have eq105000 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X5 (M.op X1 X0))) = (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104969 X2 X1 X2 X0 X1 X5
       have i₂ := eq206 X0 X1 X2 (M.op X1 X0)
       grind)
    | exact superpose eq206 eq104969
    | exact resolve eq104969 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq104969
  have eq105014 : ∀ X0 X1 X5 : G, (M.op X0 (M.op X5 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 X0))) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq105000 X0 X1 x x x X5
       have i₂ := eq12355 (M.op X5 (M.op X1 X0)) (M.op x X1) x (M.op x x) X0
       grind)
    | exact superpose eq12355 eq105000
    | exact resolve eq105000 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105000
  have eq116443 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X3))) = (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X4 (M.op X5 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq105014 X3 X5 X4
       have i₂ := eq32589 X1 X2 X0 X3
       grind)
    | exact superpose eq32589 eq105014
    | exact resolve eq105014 eq32589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105014
  have eq117160 : ∀ X0 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X3))) = (M.op (M.op X0 X3) (M.op X4 (M.op X5 X3))) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq116443 X0 x x X3 X4 X5
       have i₂ := eq12355 (M.op X4 (M.op X5 X3)) X0 x (M.op x x) (M.op X0 X3)
       grind)
    | exact superpose eq12355 eq116443
    | exact resolve eq116443 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12355 eq116443
  have eq122166 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq955 (σ y) (σ y)
       have i₂ := eq24846
       grind)
    | exact superpose eq24846 eq955
    | exact resolve eq955 eq24846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24846
  have eq122250 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq122166
  have eq122274 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq122250
  have eq135705 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq955 (σ y) (σ x)
       have i₂ := eq122274
       grind)
    | exact superpose eq122274 eq955
    | exact resolve eq955 eq122274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135814 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122274 eq135705
    | exact resolve eq135705 eq122274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122274 eq135705
  have eq167825 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (τ X2) = (M.op (τ X2) (M.op X1 (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14925 X0 X1 X2 X3
       have i₂ := eq117160 X0 X1 X1 X0
       grind)
    | exact superpose eq117160 eq14925
    | (have j0 := eq14925 X0 X1 X2 X3
       grind)
    | exact resolve eq14925 eq117160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14925 eq117160
  have eq352722 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq167825 (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0 x
       have i₂ := eq44051 (τ X0) (M.op (τ X0) (M.op (τ X0) (τ X0))) x (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq44051 eq167825
    | (have j0 := eq167825 (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0 x
       grind)
    | exact resolve eq167825 eq44051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44051 eq167825
  have eq353521 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq352722 X0
       have i₂ := eq51796 (τ X0) (τ X0) (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq51796 eq352722
    | (have j0 := eq352722 X0
       grind)
    | exact resolve eq352722 eq51796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352722
  have eq354278 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq353521 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq353521
    | (have j0 := eq353521 X0
       grind)
    | exact resolve eq353521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353521
  have eq354887 : ∀ X0 : G, (τ X0) = (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq354278 X0
       have i₂ := eq29426 (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (τ X0)
       grind)
    | exact superpose eq29426 eq354278
    | (have j0 := eq354278 X0
       grind)
    | exact resolve eq354278 eq29426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29426 eq354278
  have eq355362 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq354887 X0
       have i₂ := eq2171 (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq2171 eq354887
    | (have j0 := eq354887 X0
       grind)
    | exact resolve eq354887 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq354887
  have eq355698 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq355362 X0
       have i₂ := eq4883 (τ X0) (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq4883 eq355362
    | (have j0 := eq355362 X0
       grind)
    | exact resolve eq355362 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4883 eq355362
  have eq355897 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq355698 X0
       have i₂ := eq70 (τ X0) (τ X0) (M.op (τ X0) (τ X0)) (τ X0)
       grind)
    | exact superpose eq70 eq355698
    | (have j0 := eq355698 X0
       grind)
    | exact resolve eq355698 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq355698
  have eq356016 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq355897 X0
       have i₂ := eq51796 (τ X0) (τ X0) (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq51796 eq355897
    | (have j0 := eq355897 X0
       grind)
    | exact resolve eq355897 eq51796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51796 eq355897
  have eq356017 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq356016 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356016
  have eq356192 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq356017 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq356017
    | exact resolve eq356017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356017
  have eq356438 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq356192 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq356192
    | (have j0 := eq356192 X0
       grind)
    | exact resolve eq356192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356192
  have eq356527 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq356438 X0
       grind)
    | exact superpose eq356438 eq10
    | (have j1 := eq356438 X0
       grind)
    | exact resolve eq10 eq356438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356438
  have eq356772 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq356527 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq356527
    | (have j0 := eq356527 X0
       grind)
    | exact resolve eq356527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356527
  have eq356823 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq356772 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq356772 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq356772 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356772
  have eq356974 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq356823 (σ X0)
       grind)
    | exact superpose eq356823 eq15
    | exact resolve eq15 eq356823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357082 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq356974 X0
       have i₂ := eq356823 X0
       grind)
    | exact superpose eq356823 eq356974
    | exact resolve eq356974 eq356823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356823 eq356974
  have eq357978 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135814
       have i₂ := eq357082 y
       grind)
    | exact superpose eq357082 eq135814
    | exact resolve eq135814 eq357082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135814
  have eq358107 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq955 (σ X0) (σ X0)
       have i₂ := eq357082 X0
       grind)
    | exact superpose eq357082 eq955
    | exact resolve eq955 eq357082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357082
  have eq619648 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq357978
       grind)
    | exact superpose eq357978 eq10
    | exact resolve eq10 eq357978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357978
  have eq620066 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq619648
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq619648
    | exact resolve eq619648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619648
  have eq620067 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq620066
  have eq620386 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq955 y y
       have i₂ := eq620067
       grind)
    | exact superpose eq620067 eq955
    | exact resolve eq955 eq620067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq620067
  have eq620661 : x = (M.op x y) := by grind
  clear eq620386
  have eq620956 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq620661
       grind)
    | exact superpose eq620661 eq16
    | exact resolve eq16 eq620661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621045 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq32589 X0 X1 x y
       have i₂ := eq620661
       grind)
    | exact superpose eq620661 eq32589
    | exact resolve eq32589 eq620661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32589 eq620661
  have eq621259 : x = (M.op y y) := by
    first
    | (have i₁ := eq621045 x x
       have i₂ := eq207 x x x
       grind)
    | exact superpose eq207 eq621045
    | exact resolve eq621045 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq621045
  have eq621362 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq358107 y
       have i₂ := eq621259
       grind)
    | exact superpose eq621259 eq358107
    | exact resolve eq358107 eq621259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358107 eq621259
  have eq621803 : False := by grind
  exact eq621803

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pyx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq118 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq74
    | exact resolve eq74 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq88
    | exact resolve eq88 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq166 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq129 X0 X0 X0
       grind)
    | exact superpose eq129 eq129
    | exact resolve eq129 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq133 X2 X3 X4
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq133
    | exact resolve eq133 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq130 X2 X3
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq130
    | exact resolve eq130 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq67
    | exact resolve eq67 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq208 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq129 X2 X3 X2
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq129
    | exact resolve eq129 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X2 X2
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq88
    | exact resolve eq88 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq215 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq133 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq133 eq9
    | exact resolve eq9 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq129 X3 x X0
       grind)
    | exact superpose eq129 eq206
    | exact resolve eq206 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq890 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70 X2 X2 X3 X4
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq70
    | exact resolve eq70 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 (M.op X1 X0) X2 X3
       have i₂ := eq133 X0 X0 X1
       grind)
    | exact superpose eq133 eq70
    | exact resolve eq70 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq70 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq892 X0 X1 x x
       have i₂ := eq70 X0 X0 x x
       grind)
    | exact superpose eq70 eq892
    | exact resolve eq892 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq1104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  have eq1207 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X3 X3)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq118 X2 X3
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq118
    | exact resolve eq118 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1287 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133 X1 (M.op X2 X0) (M.op X2 (M.op X2 X2))
       have i₂ := eq118 X0 X2
       grind)
    | exact superpose eq118 eq133
    | exact resolve eq133 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 (M.op X3 X0) (M.op X3 (M.op X3 X3)) X2 X1
       have i₂ := eq118 X0 X3
       grind)
    | exact superpose eq118 eq206
    | exact resolve eq206 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1843 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq166 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq206 X1 X2 X0 X4
       grind)
    | exact superpose eq206 eq166
    | exact resolve eq166 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1879 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq166 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq166 eq9
    | exact resolve eq9 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1992 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1843 X0 X1 X2 X3 X4
       have i₂ := eq63 X4 X0
       grind)
    | exact superpose eq63 eq1843
    | exact resolve eq1843 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq2040 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1992 X0 X1 X2 X3 X4
       have i₂ := eq63 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq63 eq1992
    | exact resolve eq1992 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq2063 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2040 X0 X1 X2 X3 X4
       have i₂ := eq206 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq206 eq2040
    | exact resolve eq2040 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2068 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2063 X0 x x X3 X4
       have i₂ := eq210 x x X0
       grind)
    | exact superpose eq210 eq2063
    | exact resolve eq2063 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq2063
  have eq2087 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2068 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq166 X0 x X1
       grind)
    | exact superpose eq166 eq2068
    | exact resolve eq2068 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2155 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2087 X0 X1 X2
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq2087
    | exact resolve eq2087 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2171 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2155 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq2155
    | exact resolve eq2155 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2155
  have eq3212 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq208 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq207 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq207 eq208
    | exact resolve eq208 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3340 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3212 X0 X1 X2 X3
       have i₂ := eq2171 X0 (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq2171 eq3212
    | exact resolve eq3212 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq3396 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3340 X0 x X2 X3
       have i₂ := eq2068 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq2068 eq3340
    | exact resolve eq3340 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068 eq3340
  have eq4112 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq129 X1 x X0
       grind)
    | exact superpose eq129 eq215
    | exact resolve eq215 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq4132 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op X0 (M.op X3 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq215 X3 X2 (M.op X1 (M.op X2 X3)) X0
       have i₂ := eq133 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq133 eq215
    | exact resolve eq215 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq4238 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4112 X0 X1
       have i₂ := eq2171 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2171 eq4112
    | exact resolve eq4112 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112
  have eq4279 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4238 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq166 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq166 eq4238
    | exact resolve eq4238 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq4370 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq4238 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq4238 eq206
    | exact resolve eq206 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4396 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4370 X0 X1 X2
       have i₂ := eq2171 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2171 eq4370
    | exact resolve eq4370 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4370
  have eq4439 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4279 X0 X1
       have i₂ := eq2171 X0 X1 X1
       grind)
    | exact superpose eq2171 eq4279
    | exact resolve eq4279 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq4477 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4439 X0 X1
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq4439
    | exact resolve eq4439 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq4439
  have eq4550 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4477 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq206 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq206 eq4477
    | exact resolve eq4477 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4557 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4238 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq4477 X0 X1
       grind)
    | exact superpose eq4477 eq4238
    | exact resolve eq4238 eq4477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4637 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4557 X0 X1
       have i₂ := eq2171 (M.op X1 X0) X0 X0
       grind)
    | exact superpose eq2171 eq4557
    | exact resolve eq4557 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq4675 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4637 X0 X1
       have i₂ := eq3396 X0 X0 X1
       grind)
    | exact superpose eq3396 eq4637
    | exact resolve eq4637 eq3396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396 eq4637
  have eq4739 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4550 X2 X1 X0
       have i₂ := eq4550 X2 X1 X3
       grind)
    | (have i₁ := eq4550 X0 X1 X2
       have i₂ := eq4550 X0 X1 X1
       grind)
    | exact superpose eq4550 eq4550
    | exact resolve eq4550 eq4550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4744 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4550 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq4477 X0 X2
       grind)
    | exact superpose eq4477 eq4550
    | exact resolve eq4550 eq4477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4477
  have eq4883 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4238 X2 X1
       have i₂ := eq4550 X2 X1 X0
       grind)
    | (have i₁ := eq4238 X0 X1
       have i₂ := eq4550 X0 X1 X1
       grind)
    | exact superpose eq4550 eq4238
    | exact resolve eq4238 eq4550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238 eq4550
  have eq5898 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq4396 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq4396 eq70
    | exact resolve eq70 eq4396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396
  have eq5925 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5898 X0 X1 X2 X3
       have i₂ := eq2171 X3 X2 X2
       grind)
    | exact superpose eq2171 eq5898
    | exact resolve eq5898 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq8798 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1104 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq1104
    | (have j0 := eq1104 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq1104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq8933 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq319 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq208 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq208 eq319
    | exact resolve eq319 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq319
  have eq9166 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8933 X0 X1 X2 X3 X4
       have i₂ := eq2171 X1 X0 X0
       grind)
    | exact superpose eq2171 eq8933
    | exact resolve eq8933 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8933
  have eq9214 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9166 X0 X1 X2 X3 X4
       have i₂ := eq5925 X3 X1 X0 X1
       grind)
    | exact superpose eq5925 eq9166
    | exact resolve eq9166 eq5925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5925 eq9166
  have eq12355 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4744 (M.op X4 X0) X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq9214 X3 X4 X4 X0 X2
       grind)
    | exact superpose eq9214 eq4744
    | exact resolve eq4744 eq9214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4744 eq9214
  have eq14349 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4675 X1 X2
       have i₂ := eq4739 X2 X1 (M.op X1 (M.op X2 X1)) X0
       grind)
    | (have i₁ := eq4675 X1 X2
       have i₂ := eq4739 X0 X1 (M.op X1 (M.op X2 X1)) X2
       grind)
    | exact superpose eq4739 eq4675
    | exact resolve eq4675 eq4739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675 eq4739
  have eq14872 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (τ X2) = (M.op (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))) (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1124 X0 (M.op (M.op X3 (τ X0)) (M.op X0 (M.op X1 X0)))
       have i₂ := eq70 X0 X1 (τ X0) X3
       grind)
    | exact superpose eq70 eq1124
    | (have j0 := eq1124 X2 (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq1124 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq14907 : ∀ X0 X1 X2 X3 : G, (τ X2) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14872 X0 X1 X2 X3
       have i₂ := eq2171 (M.op X1 (M.op X0 X1)) (M.op X3 (τ X2)) (M.op X3 (τ X2))
       grind)
    | exact superpose eq2171 eq14872
    | (have j0 := eq14872 X0 X1 X2 X3
       grind)
    | exact resolve eq14872 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14872
  have eq14920 : ∀ X0 X1 X2 X3 : G, (τ X2) = (M.op (τ X2) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14907 X0 X1 X2 X3
       have i₂ := eq4883 X3 (τ X2) (M.op X1 (M.op X0 X1))
       grind)
    | exact superpose eq4883 eq14907
    | (have j0 := eq14907 X0 X1 X2 X3
       grind)
    | exact resolve eq14907 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907
  have eq14925 : ∀ X0 X1 X2 X3 : G, (τ X2) = (M.op (τ X2) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14920 X0 X1 X2 X3
       have i₂ := eq2171 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq2171 eq14920
    | (have j0 := eq14920 X0 X1 X2 X3
       grind)
    | exact resolve eq14920 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14920
  have eq24746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8798 x y
       grind)
    | exact superpose eq8798 eq16
    | (have j1 := eq8798 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq8798 x y
       grind)
    | exact resolve eq16 eq8798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8798
  have eq24846 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq24746
  have eq29426 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14349 X1 X0 X1
       have i₂ := eq899 X0 X1 X0
       grind)
    | exact superpose eq899 eq14349
    | exact resolve eq14349 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14349
  have eq32041 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq890 x x (M.op X1 (M.op X0 X1)) X2 X3
       have i₂ := eq70 X1 X0 x x
       grind)
    | exact superpose eq70 eq890
    | exact resolve eq890 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32089 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq890 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq192 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq890 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq192 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq192 eq890
    | exact resolve eq890 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq32589 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq32089 X0 X1 x x x X5 X6
       have i₂ := eq12355 X6 x x x X5
       grind)
    | exact superpose eq12355 eq32089
    | exact resolve eq32089 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32089
  have eq32623 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32041 X0 X1 X2 X3
       have i₂ := eq2171 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq2171 eq32041
    | exact resolve eq32041 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32041
  have eq32776 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32623 X0 X1 X2 X3
       have i₂ := eq899 X1 X0 X1
       grind)
    | exact superpose eq899 eq32623
    | exact resolve eq32623 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq32623
  have eq34188 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq890 (M.op X2 (M.op X3 X4)) X1 X5 X4 X3
       have i₂ := eq1207 (M.op X3 X4) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5) X0
       grind)
    | exact superpose eq1207 eq890
    | exact resolve eq890 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq34489 : ∀ X0 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X4 X5)))) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq34188 X0 x x x X4 X5
       have i₂ := eq12355 X5 x x x X4
       grind)
    | exact superpose eq12355 eq34188
    | exact resolve eq34188 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34188
  have eq36585 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (M.op (M.op X1 (M.op X1 X1)) X0) X1 x
       have i₂ := eq1287 X1 X0 x
       grind)
    | exact superpose eq1287 eq133
    | exact resolve eq133 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq36843 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36585 X0 X1
       have i₂ := eq4883 (M.op X1 (M.op X1 X1)) X0 (M.op (M.op X1 (M.op X1 X1)) X0)
       grind)
    | exact superpose eq4883 eq36585
    | exact resolve eq36585 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36585
  have eq37108 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36843 X0 X1
       have i₂ := eq2171 X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2171 eq36843
    | exact resolve eq36843 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36843
  have eq37226 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37108 X0 X1
       have i₂ := eq4883 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq4883 eq37108
    | exact resolve eq37108 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37108
  have eq44051 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X3 X1) (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1288 X1 X2 X0 X3
       have i₂ := eq4132 X0 X1 X1 X1
       grind)
    | exact superpose eq4132 eq1288
    | exact resolve eq1288 eq4132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq4132
  have eq51179 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X4) = (M.op X4 (M.op (M.op X5 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))))) (M.op X2 (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1879 X5 X2 X3 X4
       have i₂ := eq34489 X1 X0 X2
       grind)
    | exact superpose eq34489 eq1879
    | exact resolve eq1879 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879 eq34489
  have eq51796 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X4 (M.op (M.op X1 (M.op X0 X2)) (M.op X2 (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51179 X0 X1 X2 X3 X4 x
       have i₂ := eq12355 (M.op X2 (M.op X3 X4)) x X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq12355 eq51179
    | exact resolve eq51179 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51179
  have eq52581 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1287 X1 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) X2
       have i₂ := eq37226 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq37226 eq1287
    | exact resolve eq1287 eq37226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq37226
  have eq52622 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52581 X0 X1 X2
       have i₂ := eq4883 X1 (M.op X1 X1) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq4883 eq52581
    | exact resolve eq52581 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52581
  have eq52832 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52622 X0 X1 X2
       have i₂ := eq70 X1 X1 (M.op X1 X1) X1
       grind)
    | exact superpose eq70 eq52622
    | exact resolve eq52622 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52622
  have eq52944 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52832 X0 X1 X2
       have i₂ := eq4883 (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))
       grind)
    | exact superpose eq4883 eq52832
    | exact resolve eq52832 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52832
  have eq52997 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52944 X0 X1 X2
       have i₂ := eq32776 (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op X0 X0)
       grind)
    | exact superpose eq32776 eq52944
    | exact resolve eq52944 eq32776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32776 eq52944
  have eq53024 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52997 X0 X1 X2
       have i₂ := eq12355 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))) (M.op X1 (M.op X1 X1)) X1 X1 X1
       grind)
    | exact superpose eq12355 eq52997
    | exact resolve eq52997 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52997
  have eq53043 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53024 X0 X1 X2
       have i₂ := eq4883 X0 X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))
       grind)
    | exact superpose eq4883 eq53024
    | exact resolve eq53024 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53024
  have eq53053 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53043 X0 X1 X2
       have i₂ := eq2171 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2171 eq53043
    | exact resolve eq53043 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53043
  have eq53058 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53053 X0 X1 X2
       have i₂ := eq4883 X1 (M.op X1 X1) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq4883 eq53053
    | exact resolve eq53053 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53053
  have eq53062 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53058 X0 X1 X2
       have i₂ := eq70 X1 X1 (M.op X1 X1) X1
       grind)
    | exact superpose eq70 eq53058
    | exact resolve eq53058 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53058
  have eq104090 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53062 X5 (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) X1
       have i₂ := eq890 X3 X4 X0 X1 X2
       grind)
    | exact superpose eq890 eq53062
    | exact resolve eq53062 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq53062
  have eq104741 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104090 X0 X1 X2 X3 X4 X5
       have i₂ := eq2171 (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X2 X1) (M.op X2 X1)
       grind)
    | exact superpose eq2171 eq104090
    | exact resolve eq104090 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104090
  have eq104892 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104741 X0 X1 X0 X3 X4 X5
       have i₂ := eq4883 X0 X1 (M.op X3 (M.op (M.op X4 X3) X0))
       grind)
    | exact superpose eq4883 eq104741
    | exact resolve eq104741 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104741
  have eq104969 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 (M.op (M.op (M.op X4 X3) X0) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 (M.op (M.op (M.op X4 X3) X0) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104892 X0 X1 X2 X1 X4 X5
       have i₂ := eq2171 (M.op (M.op X4 X1) X0) X1 X1
       grind)
    | exact superpose eq2171 eq104892
    | exact resolve eq104892 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104892
  have eq105000 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X5 (M.op X1 X0))) = (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104969 X2 X1 X2 X0 X1 X5
       have i₂ := eq206 X0 X1 X2 (M.op X1 X0)
       grind)
    | exact superpose eq206 eq104969
    | exact resolve eq104969 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq104969
  have eq105014 : ∀ X0 X1 X5 : G, (M.op X0 (M.op X5 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 X0))) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq105000 X0 X1 x x x X5
       have i₂ := eq12355 (M.op X5 (M.op X1 X0)) (M.op x X1) x (M.op x x) X0
       grind)
    | exact superpose eq12355 eq105000
    | exact resolve eq105000 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105000
  have eq116443 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X3))) = (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X4 (M.op X5 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq105014 X3 X5 X4
       have i₂ := eq32589 X1 X2 X0 X3
       grind)
    | exact superpose eq32589 eq105014
    | exact resolve eq105014 eq32589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105014
  have eq117160 : ∀ X0 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X3))) = (M.op (M.op X0 X3) (M.op X4 (M.op X5 X3))) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq116443 X0 x x X3 X4 X5
       have i₂ := eq12355 (M.op X4 (M.op X5 X3)) X0 x (M.op x x) (M.op X0 X3)
       grind)
    | exact superpose eq12355 eq116443
    | exact resolve eq116443 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12355 eq116443
  have eq122166 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq955 (σ y) (σ y)
       have i₂ := eq24846
       grind)
    | exact superpose eq24846 eq955
    | exact resolve eq955 eq24846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24846
  have eq122250 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq122166
  have eq122274 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq122250
  have eq135705 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq955 (σ y) (σ x)
       have i₂ := eq122274
       grind)
    | exact superpose eq122274 eq955
    | exact resolve eq955 eq122274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135814 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122274 eq135705
    | exact resolve eq135705 eq122274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122274 eq135705
  have eq167825 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op (M.op X3 (τ X2)) (M.op X1 (M.op X0 X1))))) ∨ (τ X2) = (M.op (τ X2) (M.op X1 (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14925 X0 X1 X2 X3
       have i₂ := eq117160 X0 X1 X1 X0
       grind)
    | exact superpose eq117160 eq14925
    | (have j0 := eq14925 X0 X1 X2 X3
       grind)
    | exact resolve eq14925 eq117160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14925 eq117160
  have eq352722 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq167825 (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0 x
       have i₂ := eq44051 (τ X0) (M.op (τ X0) (M.op (τ X0) (τ X0))) x (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq44051 eq167825
    | (have j0 := eq167825 (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0 x
       grind)
    | exact resolve eq167825 eq44051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44051 eq167825
  have eq353521 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq352722 X0
       have i₂ := eq51796 (τ X0) (τ X0) (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq51796 eq352722
    | (have j0 := eq352722 X0
       grind)
    | exact resolve eq352722 eq51796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352722
  have eq354278 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq353521 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq353521
    | (have j0 := eq353521 X0
       grind)
    | exact resolve eq353521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353521
  have eq354887 : ∀ X0 : G, (τ X0) = (M.op (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq354278 X0
       have i₂ := eq29426 (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))) (τ X0)
       grind)
    | exact superpose eq29426 eq354278
    | (have j0 := eq354278 X0
       grind)
    | exact resolve eq354278 eq29426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29426 eq354278
  have eq355362 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq354887 X0
       have i₂ := eq2171 (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq2171 eq354887
    | (have j0 := eq354887 X0
       grind)
    | exact resolve eq354887 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq354887
  have eq355698 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq355362 X0
       have i₂ := eq4883 (τ X0) (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq4883 eq355362
    | (have j0 := eq355362 X0
       grind)
    | exact resolve eq355362 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4883 eq355362
  have eq355897 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (M.op (τ X0) (τ X0))) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq355698 X0
       have i₂ := eq70 (τ X0) (τ X0) (M.op (τ X0) (τ X0)) (τ X0)
       grind)
    | exact superpose eq70 eq355698
    | (have j0 := eq355698 X0
       grind)
    | exact resolve eq355698 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq355698
  have eq356016 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq355897 X0
       have i₂ := eq51796 (τ X0) (τ X0) (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq51796 eq355897
    | (have j0 := eq355897 X0
       grind)
    | exact resolve eq355897 eq51796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51796 eq355897
  have eq356017 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq356016 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356016
  have eq356192 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq356017 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq356017
    | exact resolve eq356017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356017
  have eq356438 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq356192 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq356192
    | (have j0 := eq356192 X0
       grind)
    | exact resolve eq356192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356192
  have eq356527 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq356438 X0
       grind)
    | exact superpose eq356438 eq10
    | (have j1 := eq356438 X0
       grind)
    | exact resolve eq10 eq356438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356438
  have eq356772 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq356527 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq356527
    | (have j0 := eq356527 X0
       grind)
    | exact resolve eq356527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356527
  have eq356823 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq356772 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq356772 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq356772 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356772
  have eq356974 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq356823 (σ X0)
       grind)
    | exact superpose eq356823 eq15
    | exact resolve eq15 eq356823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357082 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq356974 X0
       have i₂ := eq356823 X0
       grind)
    | exact superpose eq356823 eq356974
    | exact resolve eq356974 eq356823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356823 eq356974
  have eq357978 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135814
       have i₂ := eq357082 y
       grind)
    | exact superpose eq357082 eq135814
    | exact resolve eq135814 eq357082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135814
  have eq358107 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq955 (σ X0) (σ X0)
       have i₂ := eq357082 X0
       grind)
    | exact superpose eq357082 eq955
    | exact resolve eq955 eq357082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357082
  have eq619650 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq357978
       grind)
    | exact superpose eq357978 eq10
    | exact resolve eq10 eq357978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357978
  have eq620068 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq619650
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq619650
    | exact resolve eq619650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619650
  have eq620069 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq620068
  have eq620388 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq955 y y
       have i₂ := eq620069
       grind)
    | exact superpose eq620069 eq955
    | exact resolve eq955 eq620069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq620069
  have eq620663 : x = (M.op x y) := by grind
  clear eq620388
  have eq620958 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq620663
       grind)
    | exact superpose eq620663 eq16
    | exact resolve eq16 eq620663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621047 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq32589 X0 X1 x y
       have i₂ := eq620663
       grind)
    | exact superpose eq620663 eq32589
    | exact resolve eq32589 eq620663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32589 eq620663
  have eq621261 : x = (M.op y y) := by
    first
    | (have i₁ := eq621047 x x
       have i₂ := eq207 x x x
       grind)
    | exact superpose eq207 eq621047
    | exact resolve eq621047 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq621047
  have eq621364 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq358107 y
       have i₂ := eq621261
       grind)
    | exact superpose eq621261 eq358107
    | exact resolve eq358107 eq621261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358107 eq621261
  have eq621805 : False := by grind
  exact eq621805

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
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
  clear eq66 eq70
  have eq101 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq237 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq251 eq14
    | exact resolve eq14 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq536 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
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
  have eq539 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
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
  have eq573 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  have eq596 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
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
  have eq597 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq612 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
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
  have eq618 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq613
    | exact resolve eq613 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq619 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq612 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq612
    | exact resolve eq612 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq628 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq597 X0 X1 X2 X3 X4
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq597
    | exact resolve eq597 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq1564 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq251 eq254
    | exact resolve eq254 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1603 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq254 eq50
    | exact resolve eq50 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq254 eq51
    | exact resolve eq51 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1631 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq251 eq1604
    | exact resolve eq1604 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1632 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq251 eq1603
    | exact resolve eq1603 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq2005 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1631 eq1632
    | exact resolve eq1632 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq2007 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq573 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq573 X0 X0 X0
       grind)
    | exact superpose eq573 eq573
    | exact resolve eq573 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2010 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq254 eq573
    | exact resolve eq573 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq2028 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq573 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq573 X0 X0 X0
       grind)
    | exact superpose eq573 eq573
    | exact resolve eq573 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2060 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq573 X0 X0 X0
       grind)
    | exact superpose eq573 eq14
    | exact resolve eq14 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2061 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq573 X0 X0 X0
       grind)
    | exact superpose eq573 eq50
    | exact resolve eq50 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2069 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq523 (M.op x (M.op x x))
       have i₂ := eq573 x x x
       grind)
    | exact superpose eq573 eq523
    | exact resolve eq523 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq2072 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq606 (M.op x (M.op x x)) x
       have i₂ := eq573 x x x
       grind)
    | exact superpose eq573 eq606
    | exact resolve eq606 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq2111 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq251 eq2010
    | exact resolve eq2010 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2128 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1631 eq2111
    | exact resolve eq2111 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2292 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq532 X0
       have i₂ := eq2061 X0
       grind)
    | exact superpose eq2061 eq532
    | exact resolve eq532 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2368 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2292
    | exact resolve eq2292 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2292
  have eq2602 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2069 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2069
    | exact resolve eq2069 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq2649 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2602 X0 X1
       have i₂ := eq2061 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq2061 eq2602
    | exact resolve eq2602 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602
  have eq2666 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2649 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2649
    | exact resolve eq2649 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649
  have eq2791 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq2072 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2072
    | (have j0 := eq2072 y x
       grind)
    | exact resolve eq2072 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2805 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq26 eq2072
    | (have j0 := eq2072 (σ y) (σ x)
       grind)
    | exact resolve eq2072 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2834 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2072 X0 X1
       have i₂ := eq2061 X0
       grind)
    | exact superpose eq2061 eq2072
    | exact resolve eq2072 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2872 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2805
       have i₂ := eq2061 sF3
       grind)
    | exact superpose eq2061 eq2805
    | exact resolve eq2805 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805
  have eq5427 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X1 X0 X1 X0
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq539
    | exact resolve eq539 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq5436 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq536 (M.op X0 X1) X1
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq536
    | exact resolve eq536 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6428 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq619 X0 X1 X2 X3
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq619
    | exact resolve eq619 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq6430 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X1 X2))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6428 X1 X2 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq6428
    | exact resolve eq6428 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6605 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6428 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq573 x X1 X0
       grind)
    | exact superpose eq573 eq6428
    | exact resolve eq6428 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq6630 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6428 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq6428
    | exact resolve eq6428 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6685 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq6428 X0 (M.op X1 X2) (M.op X1 X2) X0
       grind)
    | exact superpose eq6428 eq14
    | exact resolve eq14 eq6428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq7152 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq628 X0 X1 X2 X3 X4
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq628
    | exact resolve eq628 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq628
  have eq7347 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7152 X0 (M.op X0 (M.op X0 X0)) X2 X3 x
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq7152
    | exact resolve eq7152 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7152
  have eq29518 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1631 eq1564
    | exact resolve eq1564 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq29519 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2005 eq29518
    | exact resolve eq29518 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29518
  have eq30935 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq596 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq2060 X0 X0 X1
       grind)
    | exact superpose eq2060 eq596
    | exact resolve eq596 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060
  have eq31036 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30935 X0 X1 x x x
       have i₂ := eq596 X0 X0 x x x
       grind)
    | exact superpose eq596 eq30935
    | exact resolve eq30935 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq30935
  have eq45354 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2007 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2007
    | (have j0 := eq2007 y x X0
       grind)
    | exact resolve eq2007 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq46195 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2666 eq14
    | exact resolve eq14 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2666
  have eq47442 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2028 (M.op X0 (M.op X0 X0)) X1 (M.op X2 X0)
       have i₂ := eq2072 X0 X2
       grind)
    | exact superpose eq2072 eq2028
    | exact resolve eq2028 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq47538 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op (M.op X0 (M.op x x)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2028 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2028
    | (have j0 := eq2028 y X0 x
       grind)
    | exact resolve eq2028 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47566 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq2028
    | (have j0 := eq2028 (σ y) X0 (σ x)
       grind)
    | exact resolve eq2028 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47614 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X2
       have i₂ := eq2028 X2 X0 X1
       grind)
    | exact superpose eq2028 eq532
    | exact resolve eq532 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq48159 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47566 X0
       have i₂ := eq2061 sF3
       grind)
    | exact superpose eq2061 eq47566
    | exact resolve eq47566 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47566
  have eq48282 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47442 X0 X1 X2
       have i₂ := eq53 X2 X0
       grind)
    | exact superpose eq53 eq47442
    | exact resolve eq47442 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47442
  have eq48563 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48282 X0 X1 X2
       have i₂ := eq2061 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq2061 eq48282
    | exact resolve eq48282 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061 eq48282
  have eq48678 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq536 eq48563
    | exact resolve eq48563 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq48563
  have eq51409 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2005 eq2128
    | exact resolve eq2128 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2128
  have eq74180 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq45354 y
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq45354
    | exact resolve eq45354 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq45354
  have eq74348 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq74180
       have i₂ := eq31036 (M.op y x) y
       grind)
    | exact superpose eq31036 eq74180
    | exact resolve eq74180 eq31036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31036 eq74180
  have eq74386 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq74348
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq74348
    | exact resolve eq74348 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74348
  have eq74409 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq46195 eq74386
    | exact resolve eq74386 eq46195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46195 eq74386
  have eq77498 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq47614
    | (have j0 := eq47614 X0 (σ x) (σ y)
       grind)
    | exact resolve eq47614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47614
  have eq98432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6630 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq2028 X0 x X1
       grind)
    | exact superpose eq2028 eq6630
    | exact resolve eq6630 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq98835 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op (M.op x y) (M.op X1 X0))) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5436 eq6630
    | exact resolve eq6630 eq5436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5436
  have eq98859 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq77498 eq6630
    | exact resolve eq6630 eq77498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77498
  have eq99201 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq6605 eq98859
    | exact resolve eq98859 eq6605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98859
  have eq99211 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op y (M.op (M.op x y) (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6630 eq98835
    | exact resolve eq98835 eq6630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98835
  have eq99318 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6630 eq98432
    | exact resolve eq98432 eq6630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98432
  have eq100400 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq99201 eq51409
    | exact resolve eq51409 eq99201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51409 eq99201
  have eq100749 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq29519 eq100400
    | exact resolve eq100400 eq29519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29519 eq100400
  have eq110649 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6605 eq6685
    | exact resolve eq6685 eq6605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6605
  have eq110675 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X3)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6685 eq6630
    | exact resolve eq6630 eq6685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6685
  have eq110893 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6630 eq110675
    | exact resolve eq110675 eq6630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110675
  have eq114373 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6630 X2 (M.op X1 X0) (M.op (M.op x x) (M.op X1 X1)) X3
       have i₂ := eq7347 X0 x x X1
       grind)
    | exact superpose eq7347 eq6630
    | exact resolve eq6630 eq7347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7347
  have eq114406 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6630 eq114373
    | exact resolve eq114373 eq6630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6630 eq114373
  have eq168405 : (M.op (M.op x y) (M.op y (M.op y y))) = (M.op (M.op x x) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq47538 eq110649
    | exact resolve eq110649 eq47538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47538
  have eq168413 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq48159 eq110649
    | exact resolve eq110649 eq48159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48159
  have eq169174 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq168413
       have i₂ := eq114406 sF2 sF2 (M.op sF4 sF4)
       grind)
    | exact superpose eq114406 eq168413
    | exact resolve eq168413 eq114406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168413
  have eq169181 : (M.op (M.op x y) (M.op y (M.op y y))) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq237 eq168405
    | exact resolve eq168405 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq168405
  have eq169515 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq251 eq169174
    | exact resolve eq169174 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq169174
  have eq169519 : y = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq2791 eq169181
    | exact resolve eq169181 eq2791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791 eq169181
  have eq169699 : (σ y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2872 eq169515
    | exact resolve eq169515 eq2872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872 eq169515
  have eq169846 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq169519
       have i₂ := eq99318 x x (M.op y sF0)
       grind)
    | (have i₁ := eq169519
       have i₂ := eq99318 x x (M.op y sF0)
       grind)
    | exact superpose eq99318 eq169519
    | exact resolve eq169519 eq99318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99318 eq169519
  have eq170093 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq169699
       have i₂ := eq114406 sF2 sF0 (M.op sF3 sF4)
       grind)
    | exact superpose eq114406 eq169699
    | exact resolve eq169699 eq114406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169699
  have eq171727 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq170093 eq110649
    | exact resolve eq110649 eq170093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110649
  have eq171920 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq171727
       have i₂ := eq53 sF3 sF4
       grind)
    | exact superpose eq53 eq171727
    | exact resolve eq171727 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq171727
  have eq171976 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1631 eq171920
    | exact resolve eq171920 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq171920
  have eq172004 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2005 eq171976
    | exact resolve eq171976 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005 eq171976
  have eq172015 : (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq172004
       have i₂ := eq114406 sF4 sF3 sF3
       grind)
    | exact superpose eq114406 eq172004
    | exact resolve eq172004 eq114406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114406 eq172004
  have eq172020 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq100749 eq172015
    | exact resolve eq172015 eq100749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100749 eq172015
  have eq264081 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq261 (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X2 X2))
       have i₂ := eq6430 X2 X0 X1
       grind)
    | exact superpose eq6430 eq261
    | exact resolve eq261 eq6430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq6430
  have eq264233 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X0 X1)) (M.op X1 (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq99211 eq264081
    | exact resolve eq264081 eq99211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99211 eq264081
  have eq266492 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ x)))) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq170093 eq264233
    | exact resolve eq264233 eq170093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170093 eq264233
  have eq288610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq74409 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq74409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq288610
    | exact resolve eq288610 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288610
  have eq288622 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq288611
       have r₂ := eq27
       grind)
    | exact resolve eq288611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288611
  have eq288626 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq288622
    | exact resolve eq288622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288622
  have eq288882 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ y) (σ x)))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq288626 eq48678
    | exact resolve eq48678 eq288626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48678
  have eq288893 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ y) (σ x)))) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq288626 eq110893
    | exact resolve eq110893 eq288626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288626
  have eq288922 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq110893 eq288893
    | exact resolve eq288893 eq110893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110893 eq288893
  have eq288931 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq266492 eq288882
    | exact resolve eq288882 eq266492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266492 eq288882
  have eq290771 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq288922 eq288931
    | exact resolve eq288931 eq288922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288922 eq288931
  have eq291405 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq290771
  have eq291961 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq291405 eq64
    | (have r₁ := eq64
       have r₂ := eq291405
       grind)
    | exact resolve eq64 eq291405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq292166 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq291405 eq5427
    | exact resolve eq5427 eq291405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5427 eq291405
  have eq292229 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq291961
  have eq292260 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq172020 eq292166
    | exact resolve eq292166 eq172020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172020 eq292166
  have eq296018 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq292229 eq74409
    | exact resolve eq74409 eq292229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74409 eq292229
  have eq296023 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq296018
  have eq296156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq296023 eq292260
    | exact resolve eq292260 eq296023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292260 eq296023
  have eq296416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq296156
  have eq296555 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq296416
       have r₂ := eq27
       grind)
    | exact resolve eq296416 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296416
  have eq296816 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq2368 x
       have i₂ := eq296555
       grind)
    | exact superpose eq296555 eq2368
    | exact resolve eq2368 eq296555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2368 eq296555
  have eq297356 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq296816 eq2834
    | exact resolve eq2834 eq296816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834 eq296816
  have eq297539 : x = y ∨ x = y := by
    first
    | exact superpose eq169846 eq297356
    | exact resolve eq297356 eq169846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169846 eq297356
  have eq297540 : x = y := by grind
  clear eq297539
  have eq297585 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq297540
       grind)
    | exact superpose eq297540 eq18
    | exact resolve eq18 eq297540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq297586 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq297540
       grind)
    | exact superpose eq297540 eq24
    | exact resolve eq24 eq297540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq297540
  have eq298111 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq297586
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq297586
    | exact resolve eq297586 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq297586
  have eq298192 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq298111 eq26
    | exact resolve eq26 eq298111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq298111
  have eq299461 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq298192 eq71
    | exact resolve eq71 eq298192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq298192
  have eq299915 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq299461
       have i₂ := eq297585
       grind)
    | exact superpose eq297585 eq299461
    | exact resolve eq299461 eq297585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297585 eq299461
  have eq300155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq299915 eq15
    | exact resolve eq15 eq299915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299915
  have eq300516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq300155
    | exact resolve eq300155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq300155
  have eq300643 : False := by grind
  exact eq300643

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq22
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
    | (have i₁ := eq62 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
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
  have eq80 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
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
  have eq118 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq70 X1 X1
       grind)
    | exact superpose eq70 eq80
    | exact resolve eq80 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq154 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq118 X0 X0 X0
       grind)
    | exact superpose eq118 eq118
    | exact resolve eq118 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq119 X2 X3
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq119
    | exact resolve eq119 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X2
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq65
    | exact resolve eq65 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq195 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq118 X2 X3 X2
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq118
    | exact resolve eq118 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X2 X2
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq80
    | exact resolve eq80 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq201 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq122 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq122 eq9
    | exact resolve eq9 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq1463 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1463 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1463
    | (have j0 := eq1463 (σ X0) (σ X1)
       grind)
    | exact resolve eq1463 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq2477 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
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
  clear eq67
  have eq2891 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op (σ X0) (σ X1)) (M.op X2 X2))) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq1464 X0 X1
       grind)
    | (have i₁ := eq9 X0 (σ X1) (σ X0)
       have i₂ := eq1464 X0 X1
       grind)
    | exact superpose eq1464 eq9
    | (have j1 := eq1464 X0 X1
       grind)
    | exact resolve eq9 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5073 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq154 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq193 X1 X2 X0 X4
       grind)
    | exact superpose eq193 eq154
    | exact resolve eq154 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5371 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5073 X0 X1 X2 X3 X4
       have i₂ := eq62 X4 X0
       grind)
    | exact superpose eq62 eq5073
    | exact resolve eq5073 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5073
  have eq5480 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5371 X0 X1 X2 X3 X4
       have i₂ := eq62 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq62 eq5371
    | exact resolve eq5371 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5371
  have eq5530 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5480 X0 X1 X2 X3 X4
       have i₂ := eq193 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq193 eq5480
    | exact resolve eq5480 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq5480
  have eq5552 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq5530 X0 x x X3 X4
       have i₂ := eq197 x x X0
       grind)
    | exact superpose eq197 eq5530
    | exact resolve eq5530 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq5530
  have eq5605 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5552 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq154 X0 x X1
       grind)
    | exact superpose eq154 eq5552
    | exact resolve eq5552 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5760 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5605 X0 X1 X2
       have i₂ := eq119 X0 X1
       grind)
    | exact superpose eq119 eq5605
    | exact resolve eq5605 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5605
  have eq5814 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5760 X0 X1 X2
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq5760
    | exact resolve eq5760 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq5760
  have eq7713 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq195 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq194 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq194 eq195
    | exact resolve eq195 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq195
  have eq7912 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7713 X0 X1 X2 X3
       have i₂ := eq5814 X0 (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq5814 eq7713
    | exact resolve eq7713 eq5814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7713
  have eq7991 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq7912 X0 x X2 X3
       have i₂ := eq5552 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq5552 eq7912
    | exact resolve eq7912 eq5552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5552 eq7912
  have eq9328 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq118 X1 x X0
       grind)
    | exact superpose eq118 eq201
    | exact resolve eq201 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq201
  have eq9464 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9328 X0 X1
       have i₂ := eq5814 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq5814 eq9328
    | exact resolve eq9328 eq5814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9328
  have eq9512 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9464 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq154 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq154 eq9464
    | exact resolve eq9464 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq9736 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9512 X0 X1
       have i₂ := eq5814 X0 X1 X1
       grind)
    | exact superpose eq5814 eq9512
    | exact resolve eq9512 eq5814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9512
  have eq9796 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9736 X0 X1
       have i₂ := eq119 X0 X1
       grind)
    | exact superpose eq119 eq9736
    | exact resolve eq9736 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq9736
  have eq9934 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9464 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq9796 X0 X1
       grind)
    | exact superpose eq9796 eq9464
    | exact resolve eq9464 eq9796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9464 eq9796
  have eq10018 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9934 X0 X1
       have i₂ := eq5814 (M.op X1 X0) X0 X0
       grind)
    | exact superpose eq5814 eq9934
    | exact resolve eq9934 eq5814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9934
  have eq10092 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10018 X0 X1
       have i₂ := eq7991 X0 X0 X1
       grind)
    | exact superpose eq7991 eq10018
    | exact resolve eq10018 eq7991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991 eq10018
  have eq23529 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op (σ X1) X0) (M.op X2 X2))) = X2 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2891 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2891
    | exact resolve eq2891 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891
  have eq23695 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op (σ X1) X0) (M.op X2 X2))) = X2 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23529 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq23529
    | (have j0 := eq23529 X0 X1 X2
       grind)
    | exact resolve eq23529 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq23529
  have eq95142 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10092 X0 X1
       have i₂ := eq2477 X0 X1 X0
       grind)
    | exact superpose eq2477 eq10092
    | exact resolve eq10092 eq2477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10092
  have eq186999 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (M.op (σ X1) (M.op X0 (M.op (M.op (σ X1) X0) (M.op (σ X1) X0)))) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23695 X0 X1 (M.op (σ X1) X0)
       have i₂ := eq2477 (M.op (σ X1) X0) (σ X1) X0
       grind)
    | exact superpose eq2477 eq23695
    | (have j0 := eq23695 X0 X1 x
       grind)
    | exact resolve eq23695 eq2477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477 eq23695
  have eq187348 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (M.op (σ X1) (M.op X0 (M.op X0 (M.op (σ X1) X0)))) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq186999 X0 X1
       have i₂ := eq5814 X0 (σ X1) (σ X1)
       grind)
    | exact superpose eq5814 eq186999
    | (have j0 := eq186999 X0 X1
       grind)
    | exact resolve eq186999 eq5814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5814 eq186999
  have eq187450 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq187348 X0 X1
       have i₂ := eq95142 X0 (σ X1)
       grind)
    | exact superpose eq95142 eq187348
    | (have j0 := eq187348 X0 X1
       grind)
    | exact resolve eq187348 eq95142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95142 eq187348
  have eq198865 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq187450 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq187450
    | exact resolve eq187450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187450
  have eq200075 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1464 X1 X0
       have i₂ := eq198865 (σ X1) (σ X0)
       grind)
    | (have i₁ := eq1464 X0 X0
       have i₂ := eq198865 X0 (σ X0)
       grind)
    | exact superpose eq198865 eq1464
    | (have j0 := eq1464 X1 X0
       have j1 := eq198865 (σ X1) (σ X0)
       grind)
    | exact resolve eq1464 eq198865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464 eq198865
  have eq200194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200075 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq200075 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq200075 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq200075 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200075
  have eq200480 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq200194 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq200194
    | (have j0 := eq200194 X0 X1
       grind)
    | exact resolve eq200194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200194
  have eq200481 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200480
  have eq201873 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq200481 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq200481
    | exact resolve eq200481 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq200481
  have eq202016 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq201873 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq201873
    | exact resolve eq201873 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201873
  have eq202040 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq202016 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq202016
    | exact resolve eq202016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202016
  have eq202059 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq202040 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq202040
    | exact resolve eq202040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202040
  have eq202104 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq202059 X0 (τ X1)
       grind)
    | exact superpose eq202059 eq28
    | exact resolve eq28 eq202059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq202181 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq202104 X0 X1
       have i₂ := eq202059 (σ X0) X1
       grind)
    | exact superpose eq202059 eq202104
    | exact resolve eq202104 eq202059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202059 eq202104
  have eq202344 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq202181 X1 X0
       grind)
    | exact superpose eq202181 eq11
    | exact resolve eq11 eq202181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202181
  have eq203659 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq202344 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq202344
    | exact resolve eq202344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202344
  have eq204488 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq203659 x y
       grind)
    | exact superpose eq203659 eq16
    | (have r₁ := eq16
       have r₂ := eq203659 x y
       grind)
    | exact resolve eq16 eq203659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203659
  have eq204722 : False := by grind
  exact eq204722

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq10
    | exact resolve eq10 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq181 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq221 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq632 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq181
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq181
    | exact resolve eq181 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq633 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq632
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq632
    | exact resolve eq632 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq633
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq633
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq633 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq633
  have eq662 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq661
  have eq8360 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq662
       grind)
    | exact superpose eq662 eq10
    | exact resolve eq10 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq8407 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq8360
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq8360
    | exact resolve eq8360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8360
  have eq8408 : (M.op x x) = (M.op y y) := by grind
  clear eq8407
  have eq8440 : ∀ X0 : G, y = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq221 X0 y
       have i₂ := eq8408
       grind)
    | exact superpose eq8408 eq221
    | exact resolve eq221 eq8408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8408
  have eq8525 : x = y := by
    first
    | (have i₁ := eq8440 x
       have i₂ := eq221 x x
       grind)
    | exact superpose eq221 eq8440
    | exact resolve eq8440 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq8440
  have eq8596 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8525
       grind)
    | exact superpose eq8525 eq16
    | exact resolve eq16 eq8525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8525
  have eq8597 : False := by grind
  exact eq8597

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq31
    | exact resolve eq31 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq64 (M.op X0 X0)
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq31 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq31 eq68
    | exact resolve eq68 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq73 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq72
    | exact resolve eq72 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq83 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq57 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq14 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq110
    | (have j0 := eq110 (σ X0) (σ X1)
       grind)
    | exact resolve eq110 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq110 X0 X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq110 X0 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq31
    | (have j1 := eq110 X1 (M.op X0 X1)
       grind)
    | exact resolve eq31 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq120 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0
       have i₂ := eq110 X0 X1
       grind)
    | (have i₁ := eq59 X0
       have i₂ := eq110 X0 (M.op X0 X0)
       grind)
    | exact superpose eq110 eq59
    | (have j1 := eq110 X0 X1
       grind)
    | exact resolve eq59 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0
       have i₂ := eq110 X0 X1
       grind)
    | (have i₁ := eq73 X0
       have i₂ := eq110 X0 (M.op X0 X0)
       grind)
    | exact superpose eq110 eq73
    | (have j1 := eq110 X0 X1
       grind)
    | exact resolve eq73 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq126 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq110 X0 (τ X1)
       grind)
    | exact superpose eq110 eq19
    | (have j1 := eq110 X0 (τ X1)
       grind)
    | exact resolve eq19 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq110
  have eq153 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq66 X1 X1
       grind)
    | exact superpose eq66 eq83
    | exact resolve eq83 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq83
  have eq156 : ∀ X1 X3 X4 : G, (M.op (M.op X1 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq30 X3 x (M.op (M.op x x) (M.op X1 X1)) X4
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq260 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq115 X0 X1
       grind)
    | (have i₁ := eq120 X1 X1
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq120
    | (have j0 := eq120 X0 X1
       have j1 := eq115 X0 X1
       grind)
    | exact resolve eq120 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq120
  have eq279 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq260 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq523 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq10
    | (have j1 := eq113 X0 X1
       grind)
    | exact resolve eq10 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq607 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = X0 ∨ (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq121 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq121
    | (have j0 := eq121 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq121 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq121
  have eq644 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq607 X0
       have j1 := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq607 X0
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq607 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq648 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq644 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq644
    | exact resolve eq644 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq644
  have eq658 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq648 X0
       have i₂ := eq279 X0 X0
       grind)
    | exact superpose eq279 eq648
    | (have j1 := eq279 X0 X0
       grind)
    | exact resolve eq648 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq648
  have eq674 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq680 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq674 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq674
    | exact resolve eq674 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq680 X0
       have i₂ := eq674 X0
       grind)
    | exact superpose eq674 eq680
    | exact resolve eq680 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq680
  have eq1330 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (M.op X0 X0) X2 X1
       have i₂ := eq153 X0 X0
       grind)
    | exact superpose eq153 eq62
    | exact resolve eq62 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq1333 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0 x (M.op X0 X0)
       have i₂ := eq156 x X0 X0
       grind)
    | exact superpose eq156 eq62
    | exact resolve eq62 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq1374 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1333 (σ X0)
       have i₂ := eq683 X0
       grind)
    | exact superpose eq683 eq1333
    | exact resolve eq1333 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1548 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X1 X3 X2
       have i₂ := eq1330 X1 X1 X0
       grind)
    | exact superpose eq1330 eq62
    | exact resolve eq62 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1569 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1548 X0 X1 x x
       have i₂ := eq62 X1 X1 x x
       grind)
    | exact superpose eq62 eq1548
    | exact resolve eq1548 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1548
  have eq1903 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126
    | exact resolve eq126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq2016 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1903 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1903
    | (have j0 := eq1903 X0 X1
       grind)
    | exact resolve eq1903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq5025 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq683 X0
       grind)
    | exact superpose eq683 eq523
    | (have j0 := eq523 X0 X1
       grind)
    | exact resolve eq523 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq683
  have eq5026 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5025 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5025
    | (have j0 := eq5025 X0 X1
       grind)
    | exact resolve eq5025 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5025
  have eq5585 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5026 y x
       grind)
    | exact superpose eq5026 eq16
    | (have j1 := eq5026 y x
       grind)
    | exact resolve eq16 eq5026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5026
  have eq5626 : x = (M.op y y) := by
    first
    | (have j1 := eq2016 x y
       grind)
    | (have r₁ := eq5585
       have r₂ := eq2016 x y
       grind)
    | exact resolve eq5585 eq2016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016 eq5585
  have eq5663 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1374 y
       have i₂ := eq5626
       grind)
    | exact superpose eq5626 eq1374
    | exact resolve eq1374 eq5626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq5699 : x = (M.op x y) := by
    first
    | (have i₁ := eq1569 y y
       have i₂ := eq5626
       grind)
    | exact superpose eq5626 eq1569
    | exact resolve eq1569 eq5626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq5626
  have eq7340 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5663
       grind)
    | exact superpose eq5663 eq16
    | exact resolve eq16 eq5663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5663
  have eq7389 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq7340
       have i₂ := eq5699
       grind)
    | exact superpose eq5699 eq7340
    | exact resolve eq7340 eq5699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5699 eq7340
  have eq7390 : False := by grind
  exact eq7390

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (M.op X1 X0) X0
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq127 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq73 X1 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq73 X1 X1
       grind)
    | exact superpose eq73 eq86
    | exact resolve eq86 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq164 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq127 X0 X0 X0
       grind)
    | exact superpose eq127 eq127
    | exact resolve eq127 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq128 X2 X3
       have i₂ := eq131 X2 X0 X1
       grind)
    | exact superpose eq131 eq128
    | exact resolve eq128 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq131 X2 X0 X1
       grind)
    | exact superpose eq131 eq66
    | exact resolve eq66 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq206 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X2 X3 X2
       have i₂ := eq131 X2 X0 X1
       grind)
    | exact superpose eq131 eq127
    | exact resolve eq127 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 X2 X2
       have i₂ := eq131 X2 X0 X1
       grind)
    | exact superpose eq131 eq86
    | exact resolve eq86 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq213 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq131 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq131 eq9
    | exact resolve eq9 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq204 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq127 X3 x X0
       grind)
    | exact superpose eq127 eq204
    | exact resolve eq204 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 X0) X2 X3
       have i₂ := eq131 X0 X0 X1
       grind)
    | exact superpose eq131 eq69
    | exact resolve eq69 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq692 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1 x x
       have i₂ := eq69 X0 X0 x x
       grind)
    | exact superpose eq69 eq644
    | exact resolve eq644 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq1401 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq164 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq204 X1 X2 X0 X4
       grind)
    | exact superpose eq204 eq164
    | exact resolve eq164 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1524 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1401 X0 X1 X2 X3 X4
       have i₂ := eq62 X4 X0
       grind)
    | exact superpose eq62 eq1401
    | exact resolve eq1401 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1564 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1524 X0 X1 X2 X3 X4
       have i₂ := eq62 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq62 eq1524
    | exact resolve eq1524 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq1582 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1564 X0 X1 X2 X3 X4
       have i₂ := eq204 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq204 eq1564
    | exact resolve eq1564 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1587 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1582 X0 x x X3 X4
       have i₂ := eq208 x x X0
       grind)
    | exact superpose eq208 eq1582
    | exact resolve eq1582 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq1582
  have eq1605 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1587 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq164 X0 x X1
       grind)
    | exact superpose eq164 eq1587
    | exact resolve eq1587 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq1664 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1605 X0 X1 X2
       have i₂ := eq128 X0 X1
       grind)
    | exact superpose eq128 eq1605
    | exact resolve eq1605 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq1605
  have eq1679 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1664 X0 X1 X2
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq1664
    | exact resolve eq1664 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1664
  have eq2590 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq205 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq205 eq206
    | exact resolve eq206 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2695 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2590 X0 X1 X2 X3
       have i₂ := eq1679 X0 (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq1679 eq2590
    | exact resolve eq2590 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2746 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2695 X0 x X2 X3
       have i₂ := eq1587 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq1587 eq2695
    | exact resolve eq2695 eq1587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587 eq2695
  have eq3397 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq213 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq127 X1 x X0
       grind)
    | exact superpose eq127 eq213
    | exact resolve eq213 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq213
  have eq3508 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3397 X0 X1
       have i₂ := eq1679 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq1679 eq3397
    | exact resolve eq3397 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3397
  have eq3675 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq3508 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq3508 eq204
    | exact resolve eq204 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq3508
  have eq3697 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3675 X0 X1 X2
       have i₂ := eq1679 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq1679 eq3675
    | exact resolve eq3675 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675
  have eq5063 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq3697 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq3697 eq69
    | exact resolve eq69 eq3697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3697
  have eq5086 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5063 X0 X1 X2 X3
       have i₂ := eq1679 X3 X2 X2
       grind)
    | exact superpose eq1679 eq5063
    | exact resolve eq5063 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5063
  have eq5809 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq5810 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5809 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5809
    | (have j0 := eq5809 (σ X0) (σ X1)
       grind)
    | exact resolve eq5809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5830 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq5809 (τ X0) X1
       grind)
    | exact superpose eq5809 eq17
    | (have j1 := eq5809 (τ X0) X1
       grind)
    | exact resolve eq17 eq5809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq6401 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5810 X0 X1
       have i₂ := eq5809 X0 X1
       grind)
    | exact superpose eq5809 eq5810
    | (have j0 := eq5810 X0 X1
       have j1 := eq5809 (σ X0) (σ X1)
       grind)
    | exact resolve eq5810 eq5809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5810
  have eq7868 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq300 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq206 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq206 eq300
    | exact resolve eq300 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq300
  have eq8080 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7868 X0 X1 X2 X3 X4
       have i₂ := eq1679 X1 X0 X0
       grind)
    | exact superpose eq1679 eq7868
    | exact resolve eq7868 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679 eq7868
  have eq8121 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8080 X0 X1 X2 X3 X4
       have i₂ := eq5086 X3 X1 X0 X1
       grind)
    | exact superpose eq5086 eq8080
    | exact resolve eq8080 eq5086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5086 eq8080
  have eq13007 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ (M.op (M.op X2 (τ X1)) (M.op X0 X0)))) ∨ (τ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5830 X0 (M.op (M.op X2 (τ X0)) (M.op X0 X0))
       have i₂ := eq9 X0 (τ X0) X2
       grind)
    | exact superpose eq9 eq5830
    | exact resolve eq5830 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5830
  have eq16499 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6401 x y
       grind)
    | exact superpose eq6401 eq16
    | (have j1 := eq6401 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6401 x y
       grind)
    | exact resolve eq16 eq6401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6401
  have eq16563 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16499
  have eq16572 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq16563
       grind)
    | exact superpose eq16563 eq9
    | exact resolve eq9 eq16563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16587 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq692 (σ y) (σ x)
       have i₂ := eq16563
       grind)
    | exact superpose eq16563 eq692
    | exact resolve eq692 eq16563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16623 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16563 eq16587
    | exact resolve eq16587 eq16563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16563 eq16587
  have eq22278 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 X0)) X0) ≠ X0 ∨ (k X0 X0) = (M.op (M.op (σ x) (M.op X0 X0)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq67 (M.op (σ x) (M.op X0 X0)) (σ y)
       have i₂ := eq16572 X0
       grind)
    | exact superpose eq16572 eq67
    | exact resolve eq67 eq16572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16572
  have eq22345 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = (M.op (M.op (σ x) (M.op X0 X0)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22278 X0
       have i₂ := eq2746 X0 (σ x) X0
       grind)
    | exact superpose eq2746 eq22278
    | (have j0 := eq22278 X0
       grind)
    | exact resolve eq22278 eq2746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22278
  have eq22362 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22345 X0
       have i₂ := eq2746 X0 (σ x) X0
       grind)
    | exact superpose eq2746 eq22345
    | (have j0 := eq22345 X0
       grind)
    | exact resolve eq22345 eq2746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22345
  have eq22367 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22362 X0
       have j1 := eq5809 X0 X0
       grind)
    | (have r₁ := eq22362 x
       have r₂ := eq5809 x x
       grind)
    | exact resolve eq22362 eq5809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5809 eq22362
  have eq22382 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22367 (σ X0)
       grind)
    | exact superpose eq22367 eq15
    | exact resolve eq15 eq22367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22404 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22367 eq22382
    | exact resolve eq22382 eq22367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22367 eq22382
  have eq22528 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16623
       have i₂ := eq22404 y
       grind)
    | exact superpose eq22404 eq16623
    | exact resolve eq16623 eq22404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16623 eq22404
  have eq22596 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq22528
  have eq22613 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq22596
       grind)
    | exact superpose eq22596 eq10
    | exact resolve eq10 eq22596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22596
  have eq22649 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22613
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22613
    | exact resolve eq22613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22613
  have eq22680 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq692 y y
       have i₂ := eq22649
       grind)
    | exact superpose eq22649 eq692
    | exact resolve eq692 eq22649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22649
  have eq22714 : x = (M.op x y) := by grind
  clear eq22680
  have eq22745 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22714
       grind)
    | exact superpose eq22714 eq16
    | exact resolve eq16 eq22714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22746 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq22714
       grind)
    | exact superpose eq22714 eq9
    | exact resolve eq9 eq22714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22758 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq205 y x X0
       have i₂ := eq22714
       grind)
    | exact superpose eq22714 eq205
    | exact resolve eq205 eq22714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq22761 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq692 y x
       have i₂ := eq22714
       grind)
    | exact superpose eq22714 eq692
    | exact resolve eq692 eq22714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq22800 : x = (M.op y y) := by
    first
    | (have i₁ := eq22761
       have i₂ := eq22714
       grind)
    | exact superpose eq22714 eq22761
    | exact resolve eq22761 eq22714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22714 eq22761
  have eq29111 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X1 (τ (σ (M.op (M.op X2 (τ (σ X1))) (M.op X0 X0))))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (σ (M.op (M.op X2 (τ (σ X1))) (M.op X0 X0)))
       have i₂ := eq13007 X0 (σ X1) X2
       grind)
    | exact superpose eq13007 eq28
    | (have j1 := eq13007 (k X1 (τ (σ (M.op (M.op X2 (τ (σ X1))) (M.op X0 X0))))) (σ X0) X2
       grind)
    | exact resolve eq28 eq13007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13007
  have eq29119 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X1 (M.op (M.op X2 (τ (σ X1))) (M.op X0 X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29111 X0 X1 X2
       have i₂ := eq10 (M.op (M.op X2 (τ (σ X1))) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq29111
    | (have j0 := eq29111 (k X1 (M.op (M.op X2 (τ (σ X1))) (M.op X0 X0))) X0 X2
       grind)
    | exact resolve eq29111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29111
  have eq29137 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X1 (M.op (M.op X2 X1) (M.op X0 X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29119 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq29119
    | (have j0 := eq29119 (k X1 (M.op (M.op X2 X1) (M.op X0 X0))) X0 X2
       grind)
    | exact resolve eq29119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29119
  have eq29148 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29137 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29137
    | (have j0 := eq29137 X0 X1 X2
       grind)
    | exact resolve eq29137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29137
  have eq29152 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29148 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq29148
    | (have j0 := eq29148 X0 X1 X2
       grind)
    | exact resolve eq29148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29148
  have eq54244 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29152 (M.op X1 (M.op X0 X1)) (M.op X0 X1) x
       have i₂ := eq8121 X0 X1 x (M.op X0 X1) X1
       grind)
    | exact superpose eq8121 eq29152
    | (have j0 := eq29152 (M.op X1 (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)) x
       grind)
    | exact resolve eq29152 eq8121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29152
  have eq54316 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54244 X0 X1
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq54244 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq54244 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq54244
  have eq55509 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op X3 X0)) X0) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54316 (M.op X2 X3) (M.op (M.op x (M.op X0 X1)) (M.op X1 X3))
       have i₂ := eq8121 X0 X1 X2 X3 x
       grind)
    | exact superpose eq8121 eq54316
    | exact resolve eq54316 eq8121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8121 eq54316
  have eq55592 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq55509 X0 x x x
       have i₂ := eq2746 X0 (M.op x (M.op x x)) x
       grind)
    | exact superpose eq2746 eq55509
    | exact resolve eq55509 eq2746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746 eq55509
  have eq55708 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55592 (σ X0)
       grind)
    | exact superpose eq55592 eq15
    | exact resolve eq15 eq55592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55755 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq55708 X0
       have i₂ := eq55592 X0
       grind)
    | exact superpose eq55592 eq55708
    | exact resolve eq55708 eq55592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55592 eq55708
  have eq56000 : ∀ X0 : G, (σ X0) = (M.op y (M.op x (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq22746 (σ X0)
       have i₂ := eq55755 X0
       grind)
    | exact superpose eq55755 eq22746
    | exact resolve eq22746 eq55755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22746 eq55755
  have eq57275 : (σ y) = (M.op y (M.op x (σ x))) := by
    first
    | (have i₁ := eq56000 y
       have i₂ := eq22800
       grind)
    | exact superpose eq22800 eq56000
    | exact resolve eq56000 eq22800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22800 eq56000
  have eq57453 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22758 (σ x)
       have i₂ := eq57275
       grind)
    | exact superpose eq57275 eq22758
    | exact resolve eq22758 eq57275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22758 eq57275
  have eq57584 : False := by grind
  exact eq57584

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyy_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
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
  have eq64 : y ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq44
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq50
    | exact resolve eq50 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq81 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq80
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq80
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq79
    | exact resolve eq79 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq230 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq233 eq52
    | exact resolve eq52 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq76 (τ X0)
       grind)
    | exact superpose eq76 eq35
    | exact resolve eq35 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq284 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq273 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq273
    | exact resolve eq273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq287 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq284
    | exact resolve eq284 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq400 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq590 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq594 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq696 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
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
  have eq697 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq698 X0 X1 X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq698
    | exact resolve eq698 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq700 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq697
    | exact resolve eq697 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq701 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq696
    | exact resolve eq696 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq836 : ∀ X0 : G, (k (k x x) (τ X0)) = (τ (k (k (σ x) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq400 (k x x) X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq400
    | exact resolve eq400 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq839 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq400 (k y x) X0
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq400
    | exact resolve eq400 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq878 : ∀ X0 : G, (τ (k (M.op (σ x) (σ x)) X0)) = (k (k x x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq836 X0
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq836
    | exact resolve eq836 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq882 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (k (M.op (σ x) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq878 X0
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq878
    | exact resolve eq878 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq1178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1179 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1178
    | exact resolve eq1178 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1182 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1179
       have r₂ := eq28
       grind)
    | exact resolve eq1179 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1184 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1182
    | exact resolve eq1182 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1188 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1184 eq65
    | (have r₁ := eq65
       have r₂ := eq1184
       grind)
    | exact resolve eq65 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1195 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1188
  have eq1281 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1195 eq89
    | exact resolve eq89 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1195
  have eq1288 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81 eq1281
    | exact resolve eq1281 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1291 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1288
       have r₂ := eq64
       grind)
    | exact resolve eq1288 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1288
  have eq1389 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq1291
       grind)
    | exact superpose eq1291 eq73
    | exact resolve eq73 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1390 : (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1291
       grind)
    | exact superpose eq1291 eq11
    | (have j0 := eq11 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq11 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391 : (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1390
  have eq1393 : (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1391
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1391
    | exact resolve eq1391 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq1394 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1389
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq1389
    | exact resolve eq1389 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1389
  have eq1396 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1393
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1393
    | exact resolve eq1393 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1402 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1394 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq11 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1403 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1402
  have eq1407 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq1403
    | exact resolve eq1403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1410 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1407
    | exact resolve eq1407 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1530 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1
       have i₂ := eq1396
       grind)
    | exact superpose eq1396 eq14
    | exact resolve eq14 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1532 : x = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52 x
       have i₂ := eq1396
       grind)
    | exact superpose eq1396 eq52
    | exact resolve eq52 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1646 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1410 eq14
    | exact resolve eq14 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1410 eq52
    | exact resolve eq52 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1669 : (σ x) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq233 eq1648
    | exact resolve eq1648 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1912 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq658 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq658 X0 X0 X0
       grind)
    | exact superpose eq658 eq658
    | exact resolve eq658 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1953 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq658 X0 X0 X0
       grind)
    | exact superpose eq658 eq51
    | exact resolve eq51 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1954 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq658 X0 X0 X0
       grind)
    | exact superpose eq658 eq52
    | exact resolve eq52 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1970 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq692 (M.op x (M.op x x)) x
       have i₂ := eq658 x x x
       grind)
    | exact superpose eq658 eq692
    | exact resolve eq692 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq2020 : x = (M.op (σ y) (M.op (σ y) (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1184 eq1532
    | exact resolve eq1532 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq2029 : x = (M.op (σ y) (M.op (σ y) (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2020
  have eq3277 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1530 (M.op sF0 sF0) x
       have i₂ := eq692 sF0 x
       grind)
    | exact superpose eq692 eq1530
    | exact resolve eq1530 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq3339 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3277
       have i₂ := eq54 sF0 sF0
       grind)
    | exact superpose eq54 eq3277
    | exact resolve eq3277 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3277
  have eq3352 : x = (M.op (M.op x y) (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq230 eq3339
    | exact resolve eq3339 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq5457 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1646 (M.op sF4 sF4) x
       have i₂ := eq692 sF4 x
       grind)
    | exact superpose eq692 eq1646
    | exact resolve eq1646 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq1646
  have eq5546 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5457
       have i₂ := eq54 sF4 sF4
       grind)
    | exact superpose eq54 eq5457
    | exact resolve eq5457 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5457
  have eq5558 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq233 eq5546
    | exact resolve eq5546 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5546
  have eq5588 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5558 eq245
    | exact resolve eq245 eq5558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq5558
  have eq5735 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X1 X0 X1 X0
       have i₂ := eq700 X0 X1
       grind)
    | exact superpose eq700 eq595
    | exact resolve eq595 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq5842 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq700 X0 X1
       grind)
    | exact superpose eq700 eq701
    | exact resolve eq701 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq5978 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5842 (M.op x sF4) (M.op X0 X0)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq5842
    | exact resolve eq5842 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5842
  have eq7937 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq699 X0 X1 X2 X3
       have i₂ := eq700 X0 X1
       grind)
    | exact superpose eq700 eq699
    | exact resolve eq699 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq8314 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7937 X1 X0 X0 X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq7937
    | exact resolve eq7937 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8340 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7937 (M.op X1 (M.op X2 X3)) (M.op X0 X0) X3 X2
       have i₂ := eq14 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq14 eq7937
    | exact resolve eq7937 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7937
  have eq20544 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1184 eq1954
    | exact resolve eq1954 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq36495 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1970 X0 X1
       have i₂ := eq20544 X0
       grind)
    | (have i₁ := eq1970 (σ y) X1
       have i₂ := eq20544 (σ y)
       grind)
    | exact superpose eq20544 eq1970
    | exact resolve eq1970 eq20544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20544
  have eq46264 : (M.op (σ y) (M.op x y)) = (M.op x (M.op (σ y) x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2029 eq36495
    | exact resolve eq36495 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq46272 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op X0 (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq52 eq36495
    | exact resolve eq36495 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46550 : (M.op (σ y) (M.op x y)) = (M.op x (M.op (σ y) x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq46264
  have eq50842 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq839 X0
       have i₂ := eq1291
       grind)
    | exact superpose eq1291 eq839
    | exact resolve eq839 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq1291
  have eq50969 : (k (M.op x x) (M.op x x)) = (τ (k (k (σ y) (σ x)) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq81 eq50842
    | exact resolve eq50842 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51077 : (M.op (M.op x x) (M.op x x)) = (τ (k (k (σ y) (σ x)) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq50969
       have i₂ := eq76 (M.op x x)
       grind)
    | exact superpose eq76 eq50969
    | exact resolve eq50969 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50969
  have eq51096 : (M.op x (M.op x x)) = (τ (k (k (σ y) (σ x)) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq51077
       have i₂ := eq54 x x
       grind)
    | exact superpose eq54 eq51077
    | exact resolve eq51077 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51077
  have eq52264 : ∀ X0 : G, (τ (k (M.op (σ x) (σ x)) X0)) = (τ (k (k (σ y) (σ x)) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq882 X0
       have i₂ := eq50842 X0
       grind)
    | exact superpose eq50842 eq882
    | exact resolve eq882 eq50842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq50842
  have eq71859 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq46272 eq52
    | exact resolve eq52 eq46272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq72016 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq46272 eq36495
    | exact resolve eq36495 eq46272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36495
  have eq72032 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq72016 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72016
  have eq72129 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq72032 x
       have i₂ := eq54 sF3 x
       grind)
    | exact superpose eq54 eq72032
    | exact resolve eq72032 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72032
  have eq72444 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1954 eq71859
    | exact resolve eq71859 eq1954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71859
  have eq72668 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq72444 X0
       have i₂ := eq1970 X0 sF4
       grind)
    | exact superpose eq1970 eq72444
    | exact resolve eq72444 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72444
  have eq73335 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq46272 eq72129
    | exact resolve eq72129 eq46272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46272
  have eq73343 : x = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq46550 eq72129
    | exact resolve eq72129 eq46550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46550 eq72129
  have eq73428 : x = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq73343
  have eq73430 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq73335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73335
  have eq75673 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq72668 eq73430
    | exact resolve eq73430 eq72668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72668 eq73430
  have eq75748 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq75673 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75673
  have eq114088 : (M.op x (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq51096 eq52264
    | exact resolve eq52264 eq51096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51096 eq52264
  have eq114156 : (M.op x (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq114088
  have eq114177 : (M.op x (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114156
       have i₂ := eq76 (M.op sF2 sF2)
       grind)
    | exact superpose eq76 eq114156
    | exact resolve eq114156 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq114156
  have eq114185 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114177
       have i₂ := eq54 sF2 sF2
       grind)
    | exact superpose eq54 eq114177
    | exact resolve eq114177 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114177
  have eq114193 : (M.op x (M.op x x)) = (τ (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114185
       have i₂ := eq1953 sF2
       grind)
    | exact superpose eq1953 eq114185
    | exact resolve eq114185 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114185
  have eq114218 : (M.op (M.op y (M.op (M.op x y) (σ x))) (M.op y (M.op (M.op x y) (σ x)))) = (σ (M.op (M.op x (M.op x x)) (M.op x (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq114193 eq287
    | exact resolve eq287 eq114193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq114193
  have eq114276 : (σ (M.op (M.op x x) (M.op x (M.op x x)))) = (M.op (M.op y (M.op (M.op x y) (σ x))) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114218
       have i₂ := eq54 x (M.op x x)
       grind)
    | exact superpose eq54 eq114218
    | exact resolve eq114218 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114218
  have eq114281 : (σ (M.op (M.op x x) (M.op x (M.op x x)))) = (M.op (M.op (M.op x y) (σ x)) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114276
       have i₂ := eq54 y (M.op sF0 sF2)
       grind)
    | exact superpose eq54 eq114276
    | exact resolve eq114276 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114276
  have eq114284 : (M.op (M.op (M.op x y) (σ x)) (M.op y (M.op (M.op x y) (σ x)))) = (σ (M.op y (M.op (M.op x y) (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114281
       have i₂ := eq700 x x
       grind)
    | exact superpose eq700 eq114281
    | exact resolve eq114281 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq114281
  have eq114286 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq51 eq114284
    | exact resolve eq114284 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114284
  have eq114287 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114286
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq114286
    | exact resolve eq114286 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114286
  have eq114307 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (σ x))) (M.op (σ x) (M.op X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq114287 eq14
    | exact resolve eq14 eq114287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114287
  have eq121842 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 X0)) (M.op y (M.op (M.op x y) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f121842_14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
      intro X0 X1
      grind
    have f121842_15 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (σ x))) (M.op (σ x) (M.op X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ y = x := by
      intro X0
      grind
    have f121842_24 : X0 ≠ (M.op (M.op (σ x) (M.op X0 X0)) (M.op y (M.op (M.op x y) X0))) := by grind
    have f121842_25 : (σ x) ≠ (σ y) := by grind
    have f121842_26 : y ≠ x := by grind
    have f121842_29 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (σ x))) (M.op (σ x) (M.op X0 X0))) = X0 ∨ y = x := by
      intro X0
      first
      | (have j0 := f121842_15 X0
         grind)
      | (have r₁ := f121842_15 X0
         have r₂ := f121842_25
         grind)
      | exact resolve f121842_15 f121842_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f121842_30 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (σ x))) (M.op (σ x) (M.op X0 X0))) = X0 := by
      intro X0
      first
      | (have j0 := f121842_29 X0
         grind)
      | (have r₁ := f121842_29 X0
         have r₂ := f121842_26
         grind)
      | exact resolve f121842_29 f121842_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f121842_106 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 X0)) (M.op y (M.op (M.op x y) X0))) = X0 := by
      intro X0
      first
      | (have i₁ := f121842_14 (M.op y (M.op (M.op x y) (σ x))) (M.op (σ x) (M.op X0 X0))
         have i₂ := f121842_30 X0
         grind)
      | exact superpose f121842_30 f121842_14
      | exact resolve f121842_14 f121842_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f121842_301 : X0 ≠ X0 := by
      first
      | (have i₁ := f121842_24
         have i₂ := f121842_106 X0
         grind)
      | exact superpose f121842_106 f121842_24
      | (have r₁ := f121842_24
         have r₂ := f121842_106 X0
         grind)
      | exact resolve f121842_24 f121842_106
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f121842_307 : False := by grind
    exact f121842_307
  clear eq114307
  have eq126490 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) X0)) (M.op y (M.op (M.op x y) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq121842 eq5735
    | exact resolve eq5735 eq121842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5735 eq121842
  have eq126586 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y (M.op (M.op x y) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq126490 X0
       have i₂ := eq54 y (M.op sF0 X0)
       grind)
    | exact superpose eq54 eq126490
    | exact resolve eq126490 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126490
  have eq127616 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq126586 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq126586
    | exact resolve eq126586 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126586
  have eq140156 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f140156_15 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0 X1
      grind
    have f140156_21 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f140156_24 : X0 ≠ (M.op (M.op x y) (M.op X0 (M.op y X0))) := by grind
    have f140156_25 : (σ x) ≠ (σ y) := by grind
    have f140156_26 : x ≠ y := by grind
    have f140156_29 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) ∨ x = y := by
      intro X0 X1
      first
      | (have j0 := f140156_15 X0 X1
         grind)
      | (have r₁ := f140156_15 X0 X1
         have r₂ := f140156_25
         grind)
      | exact resolve f140156_15 f140156_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f140156_30 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
      intro X0 X1
      first
      | (have j0 := f140156_29 X0 X1
         grind)
      | (have r₁ := f140156_29 X0 X1
         have r₂ := f140156_26
         grind)
      | exact resolve f140156_29 f140156_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f140156_85 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
      intro X0
      first
      | (have i₁ := f140156_21 X0 (M.op x y) x
         have i₂ := f140156_30 X0 x
         grind)
      | exact superpose f140156_30 f140156_21
      | exact resolve f140156_21 f140156_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f140156_109 : X0 ≠ X0 := by
      first
      | (have i₁ := f140156_24
         have i₂ := f140156_85 X0
         grind)
      | exact superpose f140156_85 f140156_24
      | (have r₁ := f140156_24
         have r₂ := f140156_85 X0
         grind)
      | exact resolve f140156_24 f140156_85
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f140156_112 : False := by grind
    exact f140156_112
  clear eq127616
  have eq141186 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq140156 eq1912
    | exact resolve eq1912 eq140156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912 eq140156
  have eq141302 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq230 eq141186
    | exact resolve eq141186 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq141186
  have eq141339 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq141302 X0 X1
       have i₂ := eq1953 (M.op X0 (M.op y X0))
       grind)
    | exact superpose eq1953 eq141302
    | exact resolve eq141302 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953 eq141302
  have eq141351 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 (M.op y (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq594 eq141339
    | exact resolve eq141339 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141339
  have eq143728 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq3352 eq141351
    | exact resolve eq141351 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352 eq141351
  have eq144428 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq143728 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143728
  have eq145108 : y = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75748 y
       have i₂ := eq144428 y
       grind)
    | exact superpose eq144428 eq75748
    | exact resolve eq75748 eq144428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75748 eq144428
  have eq145445 : y = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq145108
  have eq145816 : y = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq145445
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq145445
    | exact resolve eq145445 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145445
  have eq148625 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq145816 eq73428
    | exact resolve eq73428 eq145816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73428 eq145816
  have eq148698 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq148625
  have eq148740 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq148698 eq30
    | exact resolve eq30 eq148698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq148698
  have eq148832 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq148740
    | exact resolve eq148740 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148740
  have eq148833 : y = (M.op x y) ∨ x = y := by grind
  clear eq148832
  have eq150395 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq148833 eq21
    | exact resolve eq21 eq148833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150397 : ∀ X0 : G, (M.op y (M.op y (M.op X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq148833 eq51
    | exact resolve eq51 eq148833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq150807 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq150395
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq150395
    | exact resolve eq150395 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150395
  have eq150829 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq150807 eq27
    | exact resolve eq27 eq150807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150882 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq150807 eq1669
    | exact resolve eq1669 eq150807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq150890 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq150807 eq1954
    | exact resolve eq1954 eq150807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq150920 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq150807 eq5588
    | exact resolve eq5588 eq150807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5588
  have eq151355 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq150920
  have eq151386 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq150882
  have eq151449 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq151355
       have r₂ := eq28
       grind)
    | exact resolve eq151355 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151355
  have eq151464 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq151386
       have r₂ := eq28
       grind)
    | exact resolve eq151386 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151386
  have eq151582 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq150829 eq54
    | exact resolve eq54 eq150829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq150829
  have eq151719 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq233 eq151582
    | exact resolve eq151582 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151582
  have eq207081 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq590 X0
       have i₂ := eq150890 X0
       grind)
    | exact superpose eq150890 eq590
    | exact resolve eq590 eq150890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq207406 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq150890 eq8314
    | exact resolve eq8314 eq150890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8314 eq150890
  have eq207538 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq207406 X0
       have i₂ := eq1970 X0 sF4
       grind)
    | exact superpose eq1970 eq207406
    | exact resolve eq207406 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970 eq207406
  have eq207655 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq594 eq207538
    | exact resolve eq207538 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq207538
  have eq207904 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq233 eq207081
    | exact resolve eq207081 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq207081
  have eq212061 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq151719 eq207904
    | exact resolve eq207904 eq151719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151719 eq207904
  have eq212158 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = y := by grind
  clear eq212061
  have eq217320 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq151464 eq212158
    | exact resolve eq212158 eq151464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151464 eq212158
  have eq217418 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq217320
  have eq217478 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq217418 eq207655
    | exact resolve eq207655 eq217418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207655
  have eq217567 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq217478
  have eq219049 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq217567 eq217418
    | exact resolve eq217418 eq217567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217418 eq217567
  have eq219156 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq219049
  have eq220794 : (σ x) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq219156 eq150397
    | exact resolve eq150397 eq219156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219156
  have eq220886 : (σ x) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq220794
  have eq253016 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq151449 eq8340
    | exact resolve eq8340 eq151449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340 eq151449
  have eq254543 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5978 eq253016
    | exact resolve eq253016 eq5978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5978 eq253016
  have eq278002 : (σ y) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq254543 eq150397
    | exact resolve eq150397 eq254543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150397 eq254543
  have eq278436 : (σ y) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq278002
  have eq278909 : (σ y) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq278436
    | exact resolve eq278436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278436
  have eq289236 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq278909 eq220886
    | exact resolve eq220886 eq278909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220886 eq278909
  have eq289350 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq289236
  have eq292203 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq289350 eq150807
    | exact resolve eq150807 eq289350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150807 eq289350
  have eq292554 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq292203
  have eq292650 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq292554 eq29
    | exact resolve eq29 eq292554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq292554
  have eq293628 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq292650
    | exact resolve eq292650 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq292650
  have eq294208 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq293628 eq148833
    | exact resolve eq148833 eq293628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148833 eq293628
  have eq294415 : x = y := by grind
  clear eq294208
  have eq295029 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq294415
       grind)
    | exact superpose eq294415 eq19
    | exact resolve eq19 eq294415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq295030 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq294415
       grind)
    | exact superpose eq294415 eq25
    | exact resolve eq25 eq294415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq294415
  have eq295244 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq295030
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq295030
    | exact resolve eq295030 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq295030
  have eq295290 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq295244 eq27
    | exact resolve eq27 eq295244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq295244
  have eq296333 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq295290 eq81
    | exact resolve eq81 eq295290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq295290
  have eq296787 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq296333
       have i₂ := eq295029
       grind)
    | exact superpose eq295029 eq296333
    | exact resolve eq296333 eq295029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295029 eq296333
  have eq296951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq296787 eq15
    | exact resolve eq15 eq296787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296787
  have eq297042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq296951
    | exact resolve eq296951 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq296951
  have eq297068 : False := by grind
  exact eq297068
