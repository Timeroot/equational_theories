import equational_theories.Definability.Basic
import equational_theories.Equations.All

/-!
# Term-definability facts found by search and proved by hand

Say that a law `L` is *term-definable* from `L'` via the binary term `t`. Substituting `t` for
every `◇` in `L` yields an equation `L[t]`, and the definition unwinds to exactly `L' ⊢ L[t]`.
Searching the (complete) implication graph of the project for pairs where `L[t]` is one of the
4694 equations turns up a handful of cases where `L[t]` is *literally* `L'`, up to renaming of
variables; those are collected here, and each proof is just the hypothesis applied to the right
arguments.

Together with `TermStructural_dual` and the facts in `Law43.lean` and `Law46.lean`, the four
theorems below settle a little over 200,000 of the pairs that the definability graph had left
open.
-/

open FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- The magma operation as a two-variable term, for building `TermDefinable` witnesses. -/
private abbrev tm (a b : (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 2)) :
    (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 2) :=
  Functions.apply₂ (Sum.inl ()) a b

/-- Equation 41 `x ◇ x = y ◇ z` is term-definable from equation 40 `x ◇ x = y ◇ y`, via the
term `x □ y := x ◇ x`: on a magma where all squares agree, that operation is constant. -/
theorem Equation41_termDefinableFrom_Equation40 : Law41.TermDefinableFrom Law40 := by
  intro G M hGL
  have h40 : Equation40 G := Law40.models_iff.mp hGL
  refine ⟨⟨fun x _ ↦ M.op x x⟩, ?_, ?_⟩
  · rw [@Law41.models_iff]
    exact fun x y _ ↦ h40 x y
  · exact ⟨tm (Term.var 0) (Term.var 0), rfl⟩

/-- Equation 40 `x ◇ x = y ◇ y` is term-definable from equation 4276
`x ◇ (x ◇ x) = y ◇ (y ◇ y)`, via the term `x □ y := x ◇ (x ◇ x)`. -/
theorem Equation40_termDefinableFrom_Equation4276 : Law40.TermDefinableFrom Law4276 := by
  intro G M hGL
  have h4276 : Equation4276 G := Law4276.models_iff.mp hGL
  refine ⟨⟨fun x _ ↦ M.op x (M.op x x)⟩, ?_, ?_⟩
  · rw [@Law40.models_iff]
    exact fun x y ↦ h4276 x y
  · exact ⟨tm (Term.var 0) (tm (Term.var 0) (Term.var 0)), rfl⟩

/-- Equation 14 `x = y ◇ (x ◇ y)` is term-definable from equation 1083
`x = y ◇ ((x ◇ (y ◇ x)) ◇ y)`, via the term `x □ y := x ◇ (y ◇ x)`. -/
theorem Equation14_termDefinableFrom_Equation1083 : Law14.TermDefinableFrom Law1083 := by
  intro G M hGL
  have h1083 : Equation1083 G := Law1083.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law14.models_iff]
    exact fun x y ↦ h1083 x y
  · exact ⟨tm (Term.var 0) (tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 14 `x = y ◇ (x ◇ y)` is term-definable from equation 1719
`x = (y ◇ y) ◇ ((x ◇ x) ◇ y)`, via the term `x □ y := (x ◇ x) ◇ y`. -/
theorem Equation14_termDefinableFrom_Equation1719 : Law14.TermDefinableFrom Law1719 := by
  intro G M hGL
  have h1719 : Equation1719 G := Law1719.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) y⟩, ?_, ?_⟩
  · rw [@Law14.models_iff]
    exact fun x y ↦ h1719 x y
  · exact ⟨tm (tm (Term.var 0) (Term.var 0)) (Term.var 1), rfl⟩

end Law.MagmaLaw
