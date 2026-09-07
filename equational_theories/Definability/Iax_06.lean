import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1230`: `x = x ◇ (((x ◇ y) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation1230 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1230 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1230.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X3 : G, (M.op X0 (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq8 X0 (M.op (M.op (M.op X0 x) X0) x) X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) x)
       have i₂ := eq18 (M.op X0 X0) x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq21 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq16
  have eq51 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq21
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq21 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq261 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0
       have i₂ := eq12 (τ X0) X1
       grind)
    | (have i₁ := eq45 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq511 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq10
    | (have j1 := eq51 X0 X1
       grind)
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq572 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq511
    | (have j0 := eq511 X0 X1
       grind)
    | exact resolve eq511 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq621 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq623 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1
       have i₂ := eq572 X0 X1
       grind)
    | (have i₁ := eq21 X0
       have i₂ := eq572 (M.op X0 X0) X1
       grind)
    | exact superpose eq572 eq21
    | (have j1 := eq572 X0 X1
       grind)
    | exact resolve eq21 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq21
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq21 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1140 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq171
       have i₂ := eq623 y x
       grind)
    | exact superpose eq623 eq171
    | (have j1 := eq623 y x
       grind)
    | (have r₁ := eq171
       have r₂ := eq623 y x
       grind)
    | exact resolve eq171 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq1141 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq171
       have i₂ := eq621 y x
       grind)
    | exact superpose eq621 eq171
    | (have j1 := eq621 y x
       grind)
    | (have r₁ := eq171
       have r₂ := eq621 y x
       grind)
    | exact resolve eq171 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq1142 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq171
       have i₂ := eq572 y x
       grind)
    | exact superpose eq572 eq171
    | (have j1 := eq572 (σ y) (σ x)
       grind)
    | (have r₁ := eq171
       have r₂ := eq572 y x
       grind)
    | exact resolve eq171 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1143 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1142
  have eq1144 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1141
  have eq1145 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1140
  have eq1159 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq1143
  have eq1171 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1159
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1159
    | exact resolve eq1159 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1259 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq572 y x
       have i₂ := eq1171
       grind)
    | exact superpose eq1171 eq572
    | (have j0 := eq572 y x
       grind)
    | exact resolve eq572 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq1260 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1171
       grind)
    | exact superpose eq1171 eq9
    | exact resolve eq9 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1283 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq1259
  have eq1300 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1260
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1260
    | exact resolve eq1260 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1419 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1300
       grind)
    | exact superpose eq1300 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1426 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1419
  have eq1831 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1144
  have eq1843 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1831
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1831
    | exact resolve eq1831 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1919 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1843
       grind)
    | exact superpose eq1843 eq9
    | exact resolve eq9 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq1963 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1919
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1919
    | exact resolve eq1919 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq1964 : y = (k x y) := by grind
  clear eq1963
  have eq2027 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32 y x
       have i₂ := eq1964
       grind)
    | exact superpose eq1964 eq32
    | (have j0 := eq32 y x
       grind)
    | exact resolve eq32 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2167 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2027
  have eq3128 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq1145
       grind)
    | exact superpose eq1145 eq180
    | exact resolve eq180 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq1145
  have eq3152 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3128
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3128
    | exact resolve eq3128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3128
  have eq3153 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3152
       have r₂ := eq2167
       grind)
    | exact resolve eq3152 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3449 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq3153
       grind)
    | exact superpose eq3153 eq9
    | exact resolve eq9 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq3505 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3449
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3449
    | exact resolve eq3449 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3812 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27 x x
       have i₂ := eq3505
       grind)
    | exact superpose eq3505 eq27
    | exact resolve eq27 eq3505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3505
  have eq3820 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3812
       have r₂ := eq2167
       grind)
    | exact resolve eq3812 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq3915 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1283
       have i₂ := eq3820
       grind)
    | exact superpose eq3820 eq1283
    | exact resolve eq1283 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq3916 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1426
       have i₂ := eq3820
       grind)
    | exact superpose eq3820 eq1426
    | exact resolve eq1426 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426 eq3820
  have eq3924 : y = (M.op x x) ∨ x = y := by grind
  clear eq3916
  have eq3925 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq3915
  have eq4033 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21 x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq21
    | exact resolve eq21 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3924
  have eq4043 : x = (M.op x y) := by
    first
    | (have r₁ := eq4033
       have r₂ := eq2167
       grind)
    | exact resolve eq4033 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167 eq4033
  have eq11167 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq261
    | (have j0 := eq261 X1 (σ X0)
       grind)
    | exact resolve eq261 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq11253 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11167 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq11167
    | (have j0 := eq11167 X0 X1
       grind)
    | exact resolve eq11167 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11167
  have eq11647 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq552 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq11648 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11647 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11647
    | (have j0 := eq11647 X0
       grind)
    | exact resolve eq11647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11647
  have eq12009 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq11648 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq11648
    | (have j0 := eq11648 (σ X0)
       grind)
    | exact resolve eq11648 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11648
  have eq12024 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12009 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12009
    | (have j0 := eq12009 X0
       grind)
    | exact resolve eq12009 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12009
  have eq14851 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq188 y x
       grind)
    | exact superpose eq188 eq14
    | (have j1 := eq188 y x
       grind)
    | exact resolve eq14 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq14926 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14851
       have i₂ := eq1964
       grind)
    | exact superpose eq1964 eq14851
    | exact resolve eq14851 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964 eq14851
  have eq14933 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14926
       have i₂ := eq4043
       grind)
    | exact superpose eq4043 eq14926
    | exact resolve eq14926 eq4043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14926
  have eq16318 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12024 X0
       have i₂ := eq11253 X0 X0
       grind)
    | exact superpose eq11253 eq12024
    | (have j0 := eq12024 X0
       have j1 := eq11253 X0 X0
       grind)
    | (have r₁ := eq12024 X0
       have r₂ := eq11253 X0 X0
       grind)
    | exact resolve eq12024 eq11253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11253 eq12024
  have eq16335 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16318
  have eq16994 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16335 x
       have i₂ := eq3925
       grind)
    | exact superpose eq3925 eq16335
    | exact resolve eq16335 eq3925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925 eq16335
  have eq17137 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq16994
  have eq17215 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq929 x
       have i₂ := eq17137
       grind)
    | exact superpose eq17137 eq929
    | exact resolve eq929 eq17137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq17137
  have eq17249 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17215
  have eq17252 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17249
       have r₂ := eq14933
       grind)
    | exact resolve eq17249 eq14933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14933 eq17249
  have eq17850 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17252
       grind)
    | exact superpose eq17252 eq14
    | exact resolve eq14 eq17252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252
  have eq17887 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq17850
       have i₂ := eq4043
       grind)
    | exact superpose eq4043 eq17850
    | exact resolve eq17850 eq4043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4043 eq17850
  have eq17888 : False := by grind
  exact eq17888

/-- `Equation1230`: `x = x ◇ (((x ◇ y) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyx_pxy_Equation1230 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1230 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1230.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq22 : ∀ X0 X3 : G, (M.op X0 (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq8 X0 (M.op (M.op (M.op X0 x) X0) x) X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) x)
       have i₂ := eq22 (M.op X0 X0) x
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq189 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq14
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq14 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq13
    | exact resolve eq13 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq306 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq306
    | exact resolve eq306 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq306
  have eq463 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq313 X0
       grind)
    | exact superpose eq313 eq25
    | exact resolve eq25 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq189
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq189
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq189 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1160 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1159
  have eq1164 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1160
       have i₂ := eq313 x
       grind)
    | exact superpose eq313 eq1160
    | exact resolve eq1160 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq1160
  have eq1172 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1164
       grind)
    | exact superpose eq1164 eq9
    | exact resolve eq9 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1208 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1172
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1172
    | exact resolve eq1172 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1209 : y = (M.op x x) := by grind
  clear eq1208
  have eq1362 : x = (M.op x y) := by
    first
    | (have i₁ := eq25 x
       have i₂ := eq1209
       grind)
    | exact superpose eq1209 eq25
    | exact resolve eq25 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1366 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq463 x
       have i₂ := eq1209
       grind)
    | exact superpose eq1209 eq463
    | exact resolve eq463 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq1209
  have eq2242 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1366
       grind)
    | exact superpose eq1366 eq14
    | exact resolve eq14 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq2250 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2242
       have i₂ := eq1362
       grind)
    | exact superpose eq1362 eq2242
    | exact resolve eq2242 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362 eq2242
  have eq2251 : False := by grind
  exact eq2251

/-- `Equation1231`: `x = x ◇ (((x ◇ y) ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation1231 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1231 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1231.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X1) X0)) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X1) X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op (M.op (M.op X0 X1) X1) X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq27 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25
    | exact resolve eq25 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq25 X1 (τ X0)
       grind)
    | exact superpose eq25 eq16
    | (have j1 := eq25 X1 (τ X0)
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq132 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq27 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27 x y
       grind)
    | exact superpose eq27 eq14
    | (have j1 := eq27 x y
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq9
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1)
       have i₂ := eq27 X1 X0
       grind)
    | exact superpose eq27 eq19
    | (have j1 := eq27 X1 X0
       grind)
    | exact resolve eq19 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq413 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq465 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq413 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq413
    | (have j0 := eq413 X0 X1
       grind)
    | exact resolve eq413 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq486 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq573 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1
       have i₂ := eq465 X0 X1
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq465 (M.op X0 X0) X1
       grind)
    | exact superpose eq465 eq19
    | (have j1 := eq465 X0 X1
       grind)
    | exact resolve eq19 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq19
    | (have j1 := eq52 X0 X0
       grind)
    | exact resolve eq19 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq938 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144
       have i₂ := eq573 y x
       grind)
    | exact superpose eq573 eq144
    | (have j1 := eq573 y x
       grind)
    | (have r₁ := eq144
       have r₂ := eq573 y x
       grind)
    | exact resolve eq144 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq939 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq144
       have i₂ := eq530 x y
       grind)
    | exact superpose eq530 eq144
    | (have j1 := eq530 x y
       grind)
    | (have r₁ := eq144
       have r₂ := eq530 x y
       grind)
    | exact resolve eq144 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq940 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq144
       have i₂ := eq465 y x
       grind)
    | exact superpose eq465 eq144
    | (have j1 := eq465 (σ y) (σ x)
       grind)
    | (have r₁ := eq144
       have r₂ := eq465 y x
       grind)
    | exact resolve eq144 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq465
  have eq941 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq940
  have eq942 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq939
  have eq943 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq938
  have eq957 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19 (σ x)
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq19
    | exact resolve eq19 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq941
  have eq964 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq958
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq958
    | exact resolve eq958 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1113 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq9
    | exact resolve eq9 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1152 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1113
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1113
    | exact resolve eq1113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1195 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq160 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq1208 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1152
       grind)
    | exact superpose eq1152 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1215 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1208
  have eq1260 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq132
    | (have j0 := eq132 X1 (τ X0)
       grind)
    | exact resolve eq132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq1349 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1260 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1260
    | (have j0 := eq1260 X0 X1
       grind)
    | exact resolve eq1260 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1260
  have eq1357 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1349 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1349
    | (have j0 := eq1349 X0 X1
       grind)
    | exact resolve eq1349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1498 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq942
  have eq1506 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1498
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1498
    | exact resolve eq1498 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1564 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1506
       grind)
    | exact superpose eq1506 eq9
    | exact resolve eq9 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1605 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1564
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1564
    | exact resolve eq1564 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1606 : y = (k x y) := by grind
  clear eq1605
  have eq1750 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq1606
       grind)
    | exact superpose eq1606 eq24
    | (have j0 := eq24 y x
       grind)
    | exact resolve eq24 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1882 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1750
  have eq2906 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq151 x x
       have i₂ := eq943
       grind)
    | exact superpose eq943 eq151
    | exact resolve eq151 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq943
  have eq2927 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2906
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2906
    | exact resolve eq2906 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2906
  have eq2928 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2927
       have r₂ := eq1882
       grind)
    | exact resolve eq2927 eq1882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq3221 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2928
       grind)
    | exact superpose eq2928 eq9
    | exact resolve eq9 eq2928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928
  have eq3274 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3221
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3221
    | exact resolve eq3221 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq3408 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq3274
       grind)
    | exact superpose eq3274 eq25
    | exact resolve eq25 eq3274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3274
  have eq3415 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3408
       have r₂ := eq1882
       grind)
    | exact resolve eq3408 eq1882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3408
  have eq3843 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1215
       have i₂ := eq3415
       grind)
    | exact superpose eq3415 eq1215
    | exact resolve eq1215 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq3415
  have eq3850 : y = (M.op x x) ∨ x = y := by grind
  clear eq3843
  have eq4220 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19 x
       have i₂ := eq3850
       grind)
    | exact superpose eq3850 eq19
    | exact resolve eq19 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3850
  have eq4227 : x = (M.op x y) := by
    first
    | (have r₁ := eq4220
       have r₂ := eq1882
       grind)
    | exact resolve eq4220 eq1882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882 eq4220
  have eq6228 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq957
       grind)
    | exact superpose eq957 eq14
    | exact resolve eq14 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq6246 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6228
       have i₂ := eq4227
       grind)
    | exact superpose eq4227 eq6228
    | exact resolve eq6228 eq4227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6228
  have eq6247 : y = (M.op x x) := by grind
  clear eq6246
  have eq9362 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1195 x y
       have i₂ := eq1606
       grind)
    | exact superpose eq1606 eq1195
    | (have j0 := eq1195 x y
       grind)
    | exact resolve eq1195 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq9527 : y = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1606
       have i₂ := eq1357 x y
       grind)
    | exact superpose eq1357 eq1606
    | (have j1 := eq1357 x y
       grind)
    | exact resolve eq1606 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357 eq1606
  have eq9627 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq9527
       have i₂ := eq4227
       grind)
    | exact superpose eq4227 eq9527
    | exact resolve eq9527 eq4227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9527
  have eq9628 : y = (k x x) ∨ x = y := by grind
  clear eq9627
  have eq13684 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq757 x
       have i₂ := eq9628
       grind)
    | exact superpose eq9628 eq757
    | exact resolve eq757 eq9628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq9628
  have eq13761 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq13684
       have r₂ := eq9362
       grind)
    | exact resolve eq13684 eq9362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13684
  have eq13806 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq13761
       grind)
    | exact superpose eq13761 eq14
    | exact resolve eq14 eq13761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13761
  have eq13842 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq13806
       have i₂ := eq4227
       grind)
    | exact superpose eq4227 eq13806
    | exact resolve eq13806 eq4227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4227 eq13806
  have eq13843 : x = y := by grind
  clear eq13842
  have eq13897 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq13843
       grind)
    | exact superpose eq13843 eq14
    | exact resolve eq14 eq13843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9362
       have i₂ := eq13843
       grind)
    | exact superpose eq13843 eq9362
    | exact resolve eq9362 eq13843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9362
  have eq13925 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13922
  have eq13934 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13897
       have i₂ := eq6247
       grind)
    | exact superpose eq6247 eq13897
    | exact resolve eq13897 eq6247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6247 eq13897
  have eq13937 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq13934
       have i₂ := eq13925
       grind)
    | exact superpose eq13925 eq13934
    | exact resolve eq13934 eq13925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13925 eq13934
  have eq13940 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq13937
       have i₂ := eq13843
       grind)
    | exact superpose eq13843 eq13937
    | exact resolve eq13937 eq13843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13843 eq13937
  have eq13941 : False := by grind
  exact eq13941

/-- `Equation1234`: `x = x ◇ (((x ◇ y) ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation1234 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1234 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1234.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X2) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op (M.op (M.op X0 X1) x) x) (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (M.op X0 x) X0)
       have i₂ := eq19 X0 x
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq26 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq21 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26
    | exact resolve eq26 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq180 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1)
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq21
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq21 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq486 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq544 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq592 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1
       have i₂ := eq544 X0 X1
       grind)
    | (have i₁ := eq21 X0
       have i₂ := eq544 (M.op X0 X0) X1
       grind)
    | exact superpose eq544 eq21
    | (have j1 := eq544 X0 X1
       grind)
    | exact resolve eq21 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq894 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq21
    | (have j1 := eq50 X0 X0
       grind)
    | exact resolve eq21 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq180
       have i₂ := eq594 y x
       grind)
    | exact superpose eq594 eq180
    | (have j1 := eq594 y x
       grind)
    | (have r₁ := eq180
       have r₂ := eq594 y x
       grind)
    | exact resolve eq180 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq1103 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180
       have i₂ := eq592 y x
       grind)
    | exact superpose eq592 eq180
    | (have j1 := eq592 y x
       grind)
    | (have r₁ := eq180
       have r₂ := eq592 y x
       grind)
    | exact resolve eq180 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq180
       have i₂ := eq544 y x
       grind)
    | exact superpose eq544 eq180
    | (have j1 := eq544 (σ y) (σ x)
       grind)
    | (have r₁ := eq180
       have r₂ := eq544 y x
       grind)
    | exact resolve eq180 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1105 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1104
  have eq1106 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1103
  have eq1107 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1102
  have eq1120 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21 (σ x)
       have i₂ := eq1105
       grind)
    | exact superpose eq1105 eq21
    | exact resolve eq21 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1132 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1122
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1122
    | exact resolve eq1122 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1158 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq190
    | exact resolve eq190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1204 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1158 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1158
    | (have j0 := eq1158 X0 X1
       grind)
    | exact resolve eq1158 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1158
  have eq1221 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq544 y x
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq544
    | (have j0 := eq544 y x
       grind)
    | exact resolve eq544 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq1132
  have eq1245 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq1221
  have eq1824 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1106
  have eq1835 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1824
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1824
    | exact resolve eq1824 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1902 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1835
       grind)
    | exact superpose eq1835 eq9
    | exact resolve eq9 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1946 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1902
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1902
    | exact resolve eq1902 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq2082 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq1946
       grind)
    | exact superpose eq1946 eq31
    | (have j0 := eq31 y x
       grind)
    | exact resolve eq31 eq1946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1946
  have eq2087 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2082
  have eq2204 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2087
  have eq3068 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1107
  have eq3080 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq3068
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3068
    | exact resolve eq3068 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068
  have eq3373 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq3080
       grind)
    | exact superpose eq3080 eq9
    | exact resolve eq9 eq3080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080
  have eq3428 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq3373
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3373
    | exact resolve eq3373 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373
  have eq3429 : y = (k x y) := by grind
  clear eq3428
  have eq4235 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq14
    | exact resolve eq14 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq4639 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4235
       have i₂ := eq1245
       grind)
    | exact superpose eq1245 eq4235
    | exact resolve eq4235 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq4640 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq4639
  have eq11940 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1204 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1204
    | (have j0 := eq1204 X1 (τ X0)
       grind)
    | exact resolve eq1204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq13396 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq61 (σ x) x
       have i₂ := eq1105
       grind)
    | exact superpose eq1105 eq61
    | exact resolve eq61 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1105
  have eq13821 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13396
       have r₂ := eq4640
       grind)
    | exact resolve eq13396 eq4640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640 eq13396
  have eq13869 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13821
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13821
    | exact resolve eq13821 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13821
  have eq13878 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13869
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13869
    | exact resolve eq13869 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13869
  have eq13897 : y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26 x x
       have i₂ := eq13878
       grind)
    | exact superpose eq13878 eq26
    | exact resolve eq26 eq13878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13878
  have eq13907 : y = (M.op x x) ∨ x = y := by grind
  clear eq13897
  have eq14159 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21 x
       have i₂ := eq13907
       grind)
    | exact superpose eq13907 eq21
    | exact resolve eq21 eq13907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq13907
  have eq14181 : x = (M.op x y) := by
    first
    | (have r₁ := eq14159
       have r₂ := eq2204
       grind)
    | exact resolve eq14159 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204 eq14159
  have eq14339 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4235
       have i₂ := eq14181
       grind)
    | exact superpose eq14181 eq4235
    | exact resolve eq4235 eq14181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4235
  have eq14358 : y = (M.op x x) := by grind
  clear eq14339
  have eq14736 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (τ X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq11940 X0 x
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq11940
    | (have j0 := eq11940 X0 x
       grind)
    | exact resolve eq11940 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11940
  have eq17391 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq198 y x
       grind)
    | exact superpose eq198 eq14
    | (have j1 := eq198 y x
       grind)
    | exact resolve eq14 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq17479 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17391
       have i₂ := eq3429
       grind)
    | exact superpose eq3429 eq17391
    | exact resolve eq17391 eq3429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429 eq17391
  have eq17484 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17479
       have i₂ := eq14181
       grind)
    | exact superpose eq14181 eq17479
    | exact resolve eq17479 eq14181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17479
  have eq17646 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq894 x
       have i₂ := eq14736 x
       grind)
    | exact superpose eq14736 eq894
    | (have j1 := eq14736 x
       grind)
    | exact resolve eq894 eq14736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq14736
  have eq17700 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq17646
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq17646
    | exact resolve eq17646 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17646
  have eq17709 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq17700
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq17700
    | exact resolve eq17700 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17700
  have eq17711 : (σ x) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ x) := by
    first
    | (have r₁ := eq17709
       have r₂ := eq17484
       grind)
    | exact resolve eq17709 eq17484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17709
  have eq20686 : (σ (M.op x y)) ≠ (σ x) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17711
       grind)
    | exact superpose eq17711 eq14
    | exact resolve eq14 eq17711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17711
  have eq20742 : (σ x) ≠ (σ x) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq20686
       have i₂ := eq14181
       grind)
    | exact superpose eq14181 eq20686
    | exact resolve eq20686 eq14181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14181 eq20686
  have eq20743 : (τ y) = (τ x) := by grind
  clear eq20742
  have eq21254 : y = (σ (τ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20743
       grind)
    | exact superpose eq20743 eq10
    | exact resolve eq10 eq20743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20743
  have eq21289 : x = y := by
    first
    | (have i₁ := eq21254
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21254
    | exact resolve eq21254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21254
  have eq21859 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21289
       grind)
    | exact superpose eq21289 eq14
    | exact resolve eq14 eq21289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21889 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17484
       have i₂ := eq21289
       grind)
    | exact superpose eq21289 eq17484
    | exact resolve eq17484 eq21289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17484
  have eq21892 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21889
  have eq21900 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21859
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq21859
    | exact resolve eq21859 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14358 eq21859
  have eq21902 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq21900
       have i₂ := eq21892
       grind)
    | exact superpose eq21892 eq21900
    | exact resolve eq21900 eq21892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21892 eq21900
  have eq21905 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq21902
       have i₂ := eq21289
       grind)
    | exact superpose eq21289 eq21902
    | exact resolve eq21902 eq21289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21289 eq21902
  have eq21906 : False := by grind
  exact eq21906

/-- `Equation1235`: `x = x ◇ (((x ◇ y) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1235 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1235 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1235.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq683 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq683 (σ X0) (σ X1)
       grind)
    | exact superpose eq683 eq13
    | exact resolve eq13 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq683 X0 X1
       grind)
    | exact superpose eq683 eq691
    | exact resolve eq691 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq691
  have eq2113 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq706 x y
       grind)
    | exact superpose eq706 eq14
    | (have r₁ := eq14
       have r₂ := eq706 x y
       grind)
    | exact resolve eq14 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq2146 : False := by grind
  exact eq2146

/-- `Equation1236`: `x = x ◇ (((x ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1236 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1236 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1236.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq569 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq568 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq577 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq569 (σ X0) (σ X1)
       grind)
    | exact superpose eq569 eq13
    | exact resolve eq13 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1
       have i₂ := eq569 X0 X1
       grind)
    | exact superpose eq569 eq577
    | exact resolve eq577 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq577
  have eq1839 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq592 x y
       grind)
    | exact superpose eq592 eq14
    | (have r₁ := eq14
       have r₂ := eq592 x y
       grind)
    | exact resolve eq14 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1864 : False := by grind
  exact eq1864

/-- `Equation124`: `x = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation124 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law124 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law124.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq88 (σ X0) (σ X1)
       grind)
    | exact superpose eq88 eq13
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq104
    | exact resolve eq104 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq104
  have eq1463 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq14
    | (have r₁ := eq14
       have r₂ := eq109 x y
       grind)
    | exact resolve eq14 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1484 : False := by grind
  exact eq1484

/-- `Equation1243`: `x = x ◇ (((y ◇ x) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1243 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1243 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1243.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq88 (σ X0) (σ X1)
       grind)
    | exact superpose eq88 eq13
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq104
    | exact resolve eq104 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq104
  have eq1178 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq14
    | (have r₁ := eq14
       have r₂ := eq109 x y
       grind)
    | exact resolve eq14 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1200 : False := by grind
  exact eq1200
