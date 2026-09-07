import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation960 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y x) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e10 X0 x y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (σ x) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e30 (M.op y y)
           have i₂ := b0e10 y y y
           grind)
        | exact superpose b0e10 b0e30
        | exact resolve b0e30 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X0) (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e25 X1 X0
           grind)
        | exact superpose b0e25 b0e11
        | exact resolve b0e11 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e63 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e31 (M.op (σ y) (σ y))
           have i₂ := b0e10 (σ y) (σ y) (σ y)
           grind)
        | exact superpose b0e10 b0e31
        | exact resolve b0e31 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e156 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X1 X0
           have i₂ := b0e40 X0 X1
           grind)
        | exact superpose b0e40 b0e40
        | (have j0 := b0e40 X1 X0
           have j1 := b0e40 X1 X0
           grind)
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e172 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 (σ X1) (σ X0)
           have i₂ := b0e40 X1 X0
           grind)
        | exact superpose b0e40 b0e13
        | (have j0 := b0e13 (σ X1) (σ X0)
           have j1 := b0e40 X1 X0
           grind)
        | (have r₁ := b0e13 (σ X0) (σ X1)
           have r₂ := b0e40 X0 X1
           grind)
        | exact resolve b0e13 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e173 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e40 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e174 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e172 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e172
      have b0e175 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e174 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e174
        | (have j0 := b0e174 X0 X1
           grind)
        | exact resolve b0e174 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e174
      have b0e198 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e63
           grind)
        | exact superpose b0e63 b0e16
        | exact resolve b0e16 b0e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e199 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e40 y x
           have i₂ := b0e63
           grind)
        | exact superpose b0e63 b0e40
        | (have j0 := b0e40 y x
           grind)
        | exact resolve b0e40 b0e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e204 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e13 (σ y) (σ x)
           have i₂ := b0e63
           grind)
        | exact superpose b0e63 b0e13
        | (have j0 := b0e13 (σ y) (σ x)
           grind)
        | exact resolve b0e13 b0e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63
      have b0e205 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b0e204
           have i₂ := b0e15 y x
           grind)
        | exact superpose b0e15 b0e204
        | exact resolve b0e204 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e204
      have b0e206 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e199
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e199
        | exact resolve b0e199 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e199
      have b0e207 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e198
           have i₂ := b0e35
           grind)
        | exact superpose b0e35 b0e198
        | exact resolve b0e198 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e198
      have b0e209 : (σ y) = (σ (k y x)) := by
        first
        | (have r₁ := b0e206
           have r₂ := b0e205
           grind)
        | exact resolve b0e206 b0e205
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e205 b0e206
      have b0e230 : (k y x) = (τ (σ y)) := by
        first
        | (have i₁ := b0e11 (k y x)
           have i₂ := b0e209
           grind)
        | exact superpose b0e209 b0e11
        | exact resolve b0e11 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e231 : ∀ X0 : G, (σ (k (k y x) X0)) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 (k y x) X0
           have i₂ := b0e209
           grind)
        | exact superpose b0e209 b0e15
        | exact resolve b0e15 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e209
      have b0e242 : ∀ X0 : G, (σ (k (k y x) X0)) = (σ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e231 X0
           have i₂ := b0e15 y X0
           grind)
        | exact superpose b0e15 b0e231
        | exact resolve b0e231 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e231
      have b0e243 : y = (k y x) := by
        first
        | (have i₁ := b0e230
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e230
        | exact resolve b0e230 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230
      have b0e1796 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e175 X0 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e175
        | exact resolve b0e175 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e175
      have b0e1865 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e1796 X0 X1
           have i₂ := b0e24 X0 X1
           grind)
        | exact superpose b0e24 b0e1796
        | (have j0 := b0e1796 X0 X1
           grind)
        | exact resolve b0e1796 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1796
      have b0e1870 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e1865 X0 X1
           have i₂ := b0e24 X0 X1
           grind)
        | exact superpose b0e24 b0e1865
        | (have j0 := b0e1865 X0 X1
           grind)
        | exact resolve b0e1865 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1865
      have b0e7212 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e156 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e156
        | exact resolve b0e156 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e156
      have b0e7314 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e7212 X0 X1
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e7212
        | (have j0 := b0e7212 X0 X1
           grind)
        | exact resolve b0e7212 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e7212
      have b0e7327 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e7314 X0 X1
           have i₂ := b0e24 X0 X1
           grind)
        | exact superpose b0e24 b0e7314
        | (have j0 := b0e7314 X0 X1
           grind)
        | exact resolve b0e7314 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e7314
      have b0e7333 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b0e7327 X0 X1
           have j1 := b0e13 X0 (σ X1)
           grind)
        | (have r₁ := b0e7327 X0 X1
           have r₂ := b0e13 X0 (σ X1)
           grind)
        | exact resolve b0e7327 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7327
      have b0e24537 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1870 X0 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1870
        | exact resolve b0e1870 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1870
      have b0e27642 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e51 X0 (σ X1)
           have i₂ := b0e7333 (σ X0) X1
           grind)
        | exact superpose b0e7333 b0e51
        | (have j1 := b0e7333 (σ X0) X1
           grind)
        | exact resolve b0e51 b0e7333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e7333
      have b0e27719 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e27642 X0 X1
           have i₂ := b0e11 X1
           grind)
        | exact superpose b0e11 b0e27642
        | (have j0 := b0e27642 X0 X1
           grind)
        | exact resolve b0e27642 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27642
      have b0e27745 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e27719 X0 X1
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e27719
        | (have j0 := b0e27719 X0 X1
           grind)
        | exact resolve b0e27719 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27719
      have b0e27752 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e27745 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e27745
        | (have j0 := b0e27745 X0 X1
           grind)
        | exact resolve b0e27745 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27745
      have b0e36928 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op (k y x) X0)) ∨ (k y x) = (k (k y x) X0) := by
        intro X0
        first
        | (have i₁ := b0e242 X0
           have i₂ := b0e24537 X0 (k y x)
           grind)
        | exact superpose b0e24537 b0e242
        | (have j1 := b0e24537 X0 (k y x)
           grind)
        | exact resolve b0e242 b0e24537
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e242 b0e24537
      have b0e36951 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (k y x) = (k (k y x) X0) := by
        intro X0
        first
        | (have i₁ := b0e36928 X0
           have i₂ := b0e243
           grind)
        | exact superpose b0e243 b0e36928
        | (have j0 := b0e36928 X0
           grind)
        | exact resolve b0e36928 b0e243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36928
      have b0e36970 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ y = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e36951 X0
           have i₂ := b0e243
           grind)
        | exact superpose b0e243 b0e36951
        | (have j0 := b0e36951 X0
           grind)
        | exact resolve b0e36951 b0e243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e243 b0e36951
      have b0e555120 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ y = (k y y) := by
        first
        | (have i₁ := b0e207
           have i₂ := b0e27752 y y
           grind)
        | exact superpose b0e27752 b0e207
        | (have j1 := b0e27752 y y
           grind)
        | exact resolve b0e207 b0e27752
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27752
      have b0e555301 : y = (k y y) := by
        first
        | (have j1 := b0e36970 y
           grind)
        | (have r₁ := b0e555120
           have r₂ := b0e36970 y
           grind)
        | exact resolve b0e555120 b0e36970
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36970 b0e555120
      have b0e555523 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e173 y
           have i₂ := b0e555301
           grind)
        | exact superpose b0e555301 b0e173
        | (have j0 := b0e173 y
           grind)
        | exact resolve b0e173 b0e555301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e173
      have b0e555538 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e14 y y
           have i₂ := b0e555301
           grind)
        | exact superpose b0e555301 b0e14
        | (have j0 := b0e14 y y
           grind)
        | exact resolve b0e14 b0e555301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e555301
      have b0e555544 : y = (M.op y y) := by grind
      clear b0e555538
      have b0e555549 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b0e555523
      have b0e565653 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e207
           have i₂ := b0e555549
           grind)
        | exact superpose b0e555549 b0e207
        | exact resolve b0e207 b0e555549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e207 b0e555549
      have b0e566223 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e565653
           have i₂ := b0e555544
           grind)
        | exact superpose b0e555544 b0e565653
        | exact resolve b0e565653 b0e555544
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e555544 b0e565653
      have b0e566224 : False := by grind
      exact b0e566224
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op y x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : y ≠ y ∨ x = (k x y) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 x y
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20 : x = (k x y) := by grind
      clear b1e19
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e11
        | exact resolve b1e11 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e27 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e10 X0 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
           have i₂ := b1e10 X0 X2 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e29 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
           have i₂ := b1e10 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b1e27 (M.op y y)
           have i₂ := b1e10 y y y
           grind)
        | exact superpose b1e10 b1e27
        | exact resolve b1e27 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e37 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e21 X0 X1
           have i₂ := b1e14 (τ X0) X1
           grind)
        | exact superpose b1e14 b1e21
        | (have j1 := b1e14 (τ X0) X1
           grind)
        | exact resolve b1e21 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e54 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e26 X0 X1
           have i₂ := b1e14 X0 (σ X1)
           grind)
        | exact superpose b1e14 b1e26
        | (have j1 := b1e14 X0 (σ X1)
           grind)
        | exact resolve b1e26 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e64 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e10 X0 X0 X0
           have i₂ := b1e29 X0 X0
           grind)
        | exact superpose b1e29 b1e10
        | exact resolve b1e10 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e95 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b1e10 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
           have i₂ := b1e28 X1 x x X0
           grind)
        | exact superpose b1e28 b1e10
        | exact resolve b1e10 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e141 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e36 X1 X0
           have i₂ := b1e36 X0 X1
           grind)
        | exact superpose b1e36 b1e36
        | (have j0 := b1e36 X1 X0
           have j1 := b1e36 X1 X0
           grind)
        | exact resolve b1e36 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e142 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e36 x y
           grind)
        | exact superpose b1e36 b1e16
        | (have j1 := b1e36 x y
           grind)
        | exact resolve b1e16 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e145 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op X2 X2))) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X2 (σ X1) (σ X0)
           have i₂ := b1e36 X0 X1
           grind)
        | exact superpose b1e36 b1e10
        | (have j1 := b1e36 X0 X1
           grind)
        | exact resolve b1e10 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e146 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e36 X0 X1
           grind)
        | exact superpose b1e36 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e36 X0 X1
           grind)
        | (have r₁ := b1e13 (σ X0) (σ X1)
           have r₂ := b1e36 X0 X1
           grind)
        | exact resolve b1e13 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e156 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e36 X1 X0
           grind)
        | exact superpose b1e36 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e36 X1 X0
           grind)
        | (have r₁ := b1e13 (σ X0) (σ X1)
           have r₂ := b1e36 X0 X1
           grind)
        | exact resolve b1e13 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e157 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b1e36 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e158 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e156 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e156
      have b1e159 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e158 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e158
        | (have j0 := b1e158 X0 X1
           grind)
        | exact resolve b1e158 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e158
      have b1e161 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e146 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e146
        | (have j0 := b1e146 X0 X1
           grind)
        | exact resolve b1e146 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e146
      have b1e162 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b1e142
           have r₂ := b1e18
           grind)
        | exact resolve b1e142 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e142
      have b1e167 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e162
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e162
        | exact resolve b1e162 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e162
      have b1e168 : (σ x) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e167
           have i₂ := b1e31
           grind)
        | exact superpose b1e31 b1e167
        | exact resolve b1e167 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31 b1e167
      have b1e421 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X3)) (M.op X3 (M.op X0 (M.op X1 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e95 X3 X2 (M.op X1 X0)
           have i₂ := b1e29 X1 X0
           grind)
        | exact superpose b1e29 b1e95
        | exact resolve b1e95 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29
      have b1e447 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b1e27 (M.op X0 (M.op X0 X0))
           have i₂ := b1e95 X0 X0 X0
           grind)
        | exact superpose b1e95 b1e27
        | exact resolve b1e27 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e492 : ∀ X0 : G, (M.op X0 (M.op x (M.op y X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e64 X0
           have i₂ := b1e447 X0
           grind)
        | exact superpose b1e447 b1e64
        | exact resolve b1e64 b1e447
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e64 b1e447
      have b1e546 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
        intro X0
        first
        | (have i₁ := b1e492 (M.op X0 X0)
           have i₂ := b1e27 X0
           grind)
        | exact superpose b1e27 b1e492
        | exact resolve b1e492 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27 b1e492
      have b1e844 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13 X0 (M.op X0 X0)
           have i₂ := b1e546 X0
           grind)
        | exact superpose b1e546 b1e13
        | (have j0 := b1e13 X0 (M.op X0 X0)
           grind)
        | (have r₁ := b1e13 X0 (M.op X0 X0)
           have r₂ := b1e546 X0
           grind)
        | exact resolve b1e13 b1e546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e546
      have b1e859 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
        intro X0
        first
        | (have j0 := b1e844 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e844
      have b1e898 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e37 (σ X0) X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e37
        | exact resolve b1e37 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37
      have b1e932 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e898 X0 X1
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e898
        | (have j0 := b1e898 X0 X1
           grind)
        | exact resolve b1e898 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e898
      have b1e1255 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e159 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e159
        | exact resolve b1e159 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e159
      have b1e1304 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e1255 X0 X1
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e1255
        | (have j0 := b1e1255 X0 X1
           grind)
        | exact resolve b1e1255 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1255
      have b1e1307 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e1304 X0 X1
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e1304
        | (have j0 := b1e1304 X0 X1
           grind)
        | exact resolve b1e1304 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e1304
      have b1e3665 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e145 x y X0
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e145
        | (have j0 := b1e145 x y x
           grind)
        | exact resolve b1e145 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e145
      have b1e3722 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have j0 := b1e3665 X0
           grind)
        | (have r₁ := b1e3665 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e3665 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3665
      have b1e3735 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b1e3722 (M.op X0 (M.op X0 X0))
           have i₂ := b1e95 X0 X0 X0
           grind)
        | exact superpose b1e95 b1e3722
        | exact resolve b1e3722 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e95 b1e3722
      have b1e4474 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e161 x y
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e161
        | (have j0 := b1e161 x y
           grind)
        | exact resolve b1e161 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e161
      have b1e4477 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
      clear b1e4474
      have b1e4485 : (σ y) = (σ (k y x)) := by
        first
        | (have r₁ := b1e4477
           have r₂ := b1e18
           grind)
        | exact resolve b1e4477 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4477
      have b1e5176 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e141 X1 X0
           grind)
        | exact superpose b1e141 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e141 X1 X0
           grind)
        | (have r₁ := b1e13 (σ X0) (σ X1)
           have r₂ := b1e141 X0 X1
           grind)
        | exact resolve b1e13 b1e141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e141
      have b1e5211 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e5176 X0 X1
           have j1 := b1e13 (σ X1) (σ X0)
           grind)
        | (have r₁ := b1e5176 X0 X1
           have r₂ := b1e13 (σ X1) (σ X0)
           grind)
        | exact resolve b1e5176 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5176
      have b1e5220 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e5211 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e5211
        | (have j0 := b1e5211 X0 X1
           grind)
        | exact resolve b1e5211 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5211
      have b1e5221 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e5220 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5220
      have b1e10390 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
        intro X0
        first
        | (have i₁ := b1e5221 X0 (M.op X0 X0)
           have i₂ := b1e859 X0
           grind)
        | exact superpose b1e859 b1e5221
        | (have j0 := b1e5221 X0 (M.op X0 X0)
           grind)
        | exact resolve b1e5221 b1e859
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e859 b1e5221
      have b1e10428 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
        intro X0
        first
        | (have j0 := b1e10390 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e10390
      have b1e19202 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e1307 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e1307
        | exact resolve b1e1307 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1307
      have b1e38540 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e19202 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19202
      have b1e81973 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op (σ y) (M.op (σ y) (σ y))))) := by
        intro X0 X1
        first
        | (have i₁ := b1e421 (σ y) (σ x) X0 X1
           have i₂ := b1e3735 (σ y)
           grind)
        | exact superpose b1e3735 b1e421
        | exact resolve b1e421 b1e3735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3735
      have b1e82135 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e81973 x x
           have i₂ := b1e421 (σ y) (σ y) x x
           grind)
        | exact superpose b1e421 b1e81973
        | exact resolve b1e81973 b1e421
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e421 b1e81973
      have b1e82854 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
        first
        | (have i₁ := b1e36 y x
           have i₂ := b1e82135
           grind)
        | exact superpose b1e82135 b1e36
        | (have j0 := b1e36 y x
           grind)
        | exact resolve b1e36 b1e82135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36 b1e82135
      have b1e82976 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e82854
           have i₂ := b1e4485
           grind)
        | exact superpose b1e4485 b1e82854
        | exact resolve b1e82854 b1e4485
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4485 b1e82854
      have b1e82986 : (σ x) = (M.op (σ y) (σ y)) := by
        first
        | (have r₁ := b1e82976
           have r₂ := b1e18
           grind)
        | exact resolve b1e82976 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e82976
      have b1e83325 : (τ (σ x)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b1e54 (σ y) y
           have i₂ := b1e82986
           grind)
        | exact superpose b1e82986 b1e54
        | exact resolve b1e54 b1e82986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e83506 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b1e38540 (σ y) (σ y)
           have i₂ := b1e82986
           grind)
        | exact superpose b1e82986 b1e38540
        | (have j0 := b1e38540 (σ y) (σ y)
           grind)
        | exact resolve b1e38540 b1e82986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38540 b1e82986
      have b1e83520 : (σ y) = (σ (k y y)) ∨ (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e83506
           have i₂ := b1e15 y y
           grind)
        | exact superpose b1e15 b1e83506
        | exact resolve b1e83506 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e83506
      have b1e83594 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b1e83325
           have i₂ := b1e11 y
           grind)
        | exact superpose b1e11 b1e83325
        | exact resolve b1e83325 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e83325
      have b1e83638 : x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b1e83594
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e83594
        | exact resolve b1e83594 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e83594
      have b1e85640 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b1e932 y y
           have i₂ := b1e83638
           grind)
        | exact superpose b1e83638 b1e932
        | (have j0 := b1e932 y y
           grind)
        | exact resolve b1e932 b1e83638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e932
      have b1e85651 : y = (M.op y y) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b1e85640
           have r₂ := b1e168
           grind)
        | exact resolve b1e85640 b1e168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e168 b1e85640
      have b1e86190 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b1e10428 y
           have i₂ := b1e85651
           grind)
        | exact superpose b1e85651 b1e10428
        | exact resolve b1e10428 b1e85651
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e10428 b1e85651
      have b1e86315 : (σ y) = (σ (k y y)) := by
        first
        | (have r₁ := b1e86190
           have r₂ := b1e83520
           grind)
        | exact resolve b1e86190 b1e83520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e83520 b1e86190
      have b1e86915 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b1e86315
           have i₂ := b1e83638
           grind)
        | exact superpose b1e83638 b1e86315
        | exact resolve b1e86315 b1e83638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e83638
      have b1e86924 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e157 y
           have i₂ := b1e86315
           grind)
        | exact superpose b1e86315 b1e157
        | (have j0 := b1e157 y
           grind)
        | (have r₁ := b1e157 y
           have r₂ := b1e86315
           grind)
        | exact resolve b1e157 b1e86315
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e157 b1e86315
      have b1e86987 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b1e86924
      have b1e86988 : (σ x) = (σ y) := by grind
      clear b1e86915
      have b1e87388 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e86988
           grind)
        | exact superpose b1e86988 b1e18
        | exact resolve b1e18 b1e86988
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e86988
      have b1e87482 : False := by grind
      exact b1e87482
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op y x) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 (σ x) (σ y)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : (σ x) = (k (σ x) (σ y)) := by grind
      clear b2e19
      have b2e21 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e20
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e20
        | exact resolve b2e20 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e26 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e21
           grind)
        | exact superpose b2e21 b2e11
        | exact resolve b2e11 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27 : x = (k x y) := by
        first
        | (have i₁ := b2e26
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e26
        | exact resolve b2e26 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26
      have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
           have i₂ := b2e10 X0 X2 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e32 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
           have i₂ := b2e10 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e42 : x = (M.op x y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b2e27
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e27
        | (have j1 := b2e14 y x
           grind)
        | exact resolve b2e27 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e43 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b2e21
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e21
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e21 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e44 : (σ (M.op x y)) = (σ x) := by
        first
        | (have r₁ := b2e43
           have r₂ := b2e17
           grind)
        | exact resolve b2e43 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e43
      have b2e45 : x = (M.op x y) := by
        first
        | (have r₁ := b2e42
           have r₂ := b2e17
           grind)
        | exact resolve b2e42 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e42
      have b2e47 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e10 X0 y x
           have i₂ := b2e45
           grind)
        | exact superpose b2e45 b2e10
        | exact resolve b2e10 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e23 X1 X0
           grind)
        | exact superpose b2e23 b2e11
        | exact resolve b2e11 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23
      have b2e74 : (M.op y x) = (M.op x x) := by
        first
        | (have i₁ := b2e32 x y
           have i₂ := b2e45
           grind)
        | exact superpose b2e45 b2e32
        | exact resolve b2e32 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e75 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e10 X0 X0 X0
           have i₂ := b2e32 X0 X0
           grind)
        | exact superpose b2e32 b2e10
        | exact resolve b2e10 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e98 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e31 X4 X2 X3 (M.op X1 X0)
           have i₂ := b2e32 X1 X0
           grind)
        | exact superpose b2e32 b2e31
        | exact resolve b2e31 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e108 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b2e10 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
           have i₂ := b2e31 X1 x x X0
           grind)
        | exact superpose b2e31 b2e10
        | exact resolve b2e10 b2e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e232 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e56 X0 X1
           have i₂ := b2e14 (σ X0) X1
           grind)
        | exact superpose b2e14 b2e56
        | (have j1 := b2e14 (σ X0) X1
           grind)
        | exact resolve b2e56 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56
      have b2e417 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X3)) (M.op X3 (M.op X0 (M.op X1 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e108 X3 X2 (M.op X1 X0)
           have i₂ := b2e32 X1 X0
           grind)
        | exact superpose b2e32 b2e108
        | exact resolve b2e108 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32
      have b2e443 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (M.op X0 (M.op X0 X0)) X1 X2
           have i₂ := b2e108 X0 X0 X0
           grind)
        | exact superpose b2e108 b2e10
        | exact resolve b2e10 b2e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e447 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b2e47 (M.op X0 (M.op X0 X0))
           have i₂ := b2e108 X0 X0 X0
           grind)
        | exact superpose b2e108 b2e47
        | exact resolve b2e47 b2e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47 b2e108
      have b2e663 : (M.op y x) = (M.op y (M.op y y)) := by
        first
        | (have i₁ := b2e447 y
           have i₂ := b2e45
           grind)
        | exact superpose b2e45 b2e447
        | exact resolve b2e447 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45 b2e447
      have b2e738 : y = (M.op y (M.op y x)) := by
        first
        | (have i₁ := b2e75 y
           have i₂ := b2e663
           grind)
        | exact superpose b2e663 b2e75
        | exact resolve b2e75 b2e663
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e75 b2e663
      have b2e8180 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e98 X0 (M.op X1 X0) X2 X3 X4
           have i₂ := b2e443 X0 X0 X1
           grind)
        | exact superpose b2e443 b2e98
        | exact resolve b2e98 b2e443
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e98 b2e443
      have b2e8247 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e8180 X0 X1 x x x
           have i₂ := b2e417 X0 X0 (M.op x x) x
           grind)
        | exact superpose b2e417 b2e8180
        | exact resolve b2e8180 b2e417
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e417 b2e8180
      have b2e8488 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e8247 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e8247
        | exact resolve b2e8247 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8247
      have b2e8649 : (σ y) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e8488
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e8488
        | exact resolve b2e8488 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8488
      have b2e17104 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e232 x (σ x)
           have i₂ := b2e8649
           grind)
        | exact superpose b2e8649 b2e232
        | exact resolve b2e232 b2e8649
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e232
      have b2e17156 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e17104
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e17104
        | exact resolve b2e17104 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17104
      have b2e17173 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e17156
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e17156
        | exact resolve b2e17156 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17156
      have b2e17183 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e14 x x
           have i₂ := b2e17173
           grind)
        | exact superpose b2e17173 b2e14
        | (have j0 := b2e14 x x
           grind)
        | exact resolve b2e14 b2e17173
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17173
      have b2e17193 : y = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e17183
           have i₂ := b2e74
           grind)
        | exact superpose b2e74 b2e17183
        | exact resolve b2e17183 b2e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17183
      have b2e17201 : x = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b2e17193
           have r₂ := b2e17
           grind)
        | exact resolve b2e17193 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17193
      have b2e17206 : x = (M.op y x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e17201
           have i₂ := b2e74
           grind)
        | exact superpose b2e74 b2e17201
        | exact resolve b2e17201 b2e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e74 b2e17201
      have b2e17301 : y = (M.op y x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e738
           have i₂ := b2e17206
           grind)
        | exact superpose b2e17206 b2e738
        | exact resolve b2e738 b2e17206
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e738 b2e17206
      have b2e17383 : (σ x) = (σ y) := by
        first
        | (have r₁ := b2e17301
           have r₂ := b2e17
           grind)
        | exact resolve b2e17301 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17301
      have b2e17556 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e17383
           grind)
        | exact superpose b2e17383 b2e16
        | exact resolve b2e16 b2e17383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e17565 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e8649
           have i₂ := b2e17383
           grind)
        | exact superpose b2e17383 b2e8649
        | exact resolve b2e8649 b2e17383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8649
      have b2e17627 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b2e17556
           have i₂ := b2e17565
           grind)
        | exact superpose b2e17565 b2e17556
        | exact resolve b2e17556 b2e17565
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17556 b2e17565
      have b2e17628 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e17627
           have i₂ := b2e44
           grind)
        | exact superpose b2e44 b2e17627
        | exact resolve b2e17627 b2e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44 b2e17627
      have b2e17629 : False := by grind
      exact b2e17629
    · have b3e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op y x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X0 X1
           have i₂ := b3e14 (σ X0) (σ X1)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X0) (σ X1)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e105 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e29 x y
           grind)
        | exact superpose b3e29 b3e16
        | (have j1 := b3e29 x y
           grind)
        | exact resolve b3e16 b3e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e29
      have b3e123 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e105
           have r₂ := b3e18
           grind)
        | exact resolve b3e105 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e105
      have b3e128 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e123
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e123
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e123 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e123
      have b3e129 : y = (M.op y x) := by grind
      clear b3e128
      have b3e130 : False := by grind
      exact b3e130
