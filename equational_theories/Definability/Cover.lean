import equational_theories.Definability.Basic
import equational_theories.Equations.All
import equational_theories.Superposition
import Mathlib.Tactic.ByContra

/-!
# A cover of the term-definability facts that Vampire can prove

A search over binary terms `t` of at most five operations, testing each candidate against a bank
of finite models of the source law and then handing the survivors to Vampire, turns up 3225 pairs
`(L, L')` with a proof of `L' ⊢ L[t]`, i.e. with `L` term-definable from `L'`. Almost all of them
are consequences of a few: `TermDefinable.trans` composes the relation, so a fact `L ≤ L'` also
delivers `L₁ ≤ L₂` for every `L₁` definable from `L` and every `L₂` from which `L'` is definable.

Greedily picking the fact that carries the most new pairs, the 28 theorems below transitively
cover 3167 of the 3225, or 98.2%. Each is proved the same way: give the witness term as the
operation of a new magma on the same carrier, then check the law -- an ordinary equational
implication in the original magma, transcribed here from Vampire's superposition proof.
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

/-- Equation 3211 `x = (((y ◇ z) ◇ z) ◇ x) ◇ y` is term-definable from equation 3182 `x = (((y ◇ z) ◇ x) ◇ y) ◇ z`,
via the term `x □ y := x ◇ (x ◇ (y ◇ x))`. -/
private theorem law3211_of_law3182 [Magma G] (h : Equation3182 G) :
    ∀ x y z : G, x = (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y)))))) ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y)))))) ◇ (x ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y))))))))) ◇ ((((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y)))))) ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y)))))) ◇ (x ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y))))))))) ◇ (y ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y)))))) ◇ (((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y)))))) ◇ (x ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ ((y ◇ (y ◇ (z ◇ y))) ◇ (z ◇ (y ◇ (y ◇ (z ◇ y))))))))))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))) ◇ ((((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))) ◇ (sK1 ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X2) = X3 := superpose eq8 eq8
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) = X3 := superpose eq8 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq8
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq11 eq8
  have eq25 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X3)) = X2 := superpose eq11 eq10
  have eq32 (X0 X1 X2 X3 : G) : (((X3 ◇ X1) ◇ X2) ◇ X3) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq10 eq11
  have eq37 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X3)) := superpose eq8 eq15
  have eq40 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq15 eq15
  have eq49 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq15 eq11
  have eq50 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq15 eq8
  have eq57 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq50 eq49
  have eq60 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq50 eq37
  have eq83 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq16 eq11
  have eq85 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq16 eq15
  have eq97 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X0 ◇ X2) := superpose eq11 eq57
  have eq350 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X4 ◇ X0) ◇ X2) ◇ X4)) = (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) := superpose eq12 eq15
  have eq351 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X0) ◇ X2) ◇ X3) ◇ X4) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X4)) := superpose eq12 eq15
  have eq355 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (((X3 ◇ X0) ◇ X2) ◇ X3)) := superpose eq12 eq57
  have eq356 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq50 eq355
  have eq360 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X4)) = ((X3 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) := superpose eq85 eq351
  have eq361 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X4 ◇ X0) ◇ X2) ◇ X4)) = (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) := superpose eq85 eq350
  have eq405 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X4)) = ((X2 ◇ X0) ◇ X4) := superpose eq40 eq360
  have eq406 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X4 ◇ X0) ◇ X2) ◇ X4)) = (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) := superpose eq85 eq361
  have eq436 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) := superpose eq50 eq406
  have eq792 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq16 eq50
  have eq846 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X1) ◇ X0) := superpose eq50 eq57
  have eq1238 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq15 eq60
  have eq1338 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq792 eq1238
  have eq4202 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X5))) ◇ X1) = ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X0) := superpose eq25 eq32
  have eq4490 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X0) = (((X3 ◇ X0) ◇ (X4 ◇ X5)) ◇ X2) := superpose eq50 eq4202
  have eq4693 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X0) = (X3 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X2)) := superpose eq85 eq4490
  have eq8860 (X0 : G) : sK0 ≠ ((((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))) ◇ (X0 ◇ (sK1 ◇ X0))) := superpose eq356 eq9
  have eq8912 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))) ◇ (X0 ◇ (sK1 ◇ X0)))) := superpose eq85 eq8860
  have eq9093 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))) ◇ (X0 ◇ (sK1 ◇ X0)))) := superpose eq792 eq8912
  have eq9225 (X0 : G) : sK0 ≠ ((sK2 ◇ (sK1 ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))))) ◇ (X0 ◇ (sK1 ◇ X0))) := superpose eq83 eq9093
  have eq9310 (X0 : G) : sK0 ≠ ((sK1 ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))) ◇ ((sK2 ◇ X0) ◇ (sK1 ◇ X0))) := superpose eq792 eq9225
  have eq9371 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((((sK2 ◇ X0) ◇ (sK1 ◇ X0)) ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))) ◇ sK1)) := superpose eq4693 eq9310
  have eq9412 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (((sK2 ◇ X0) ◇ (sK1 ◇ X0)) ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))))) ◇ sK1)) := superpose eq792 eq9371
  have eq9441 (X0 : G) : sK0 ≠ ((sK2 ◇ (sK1 ◇ (((sK2 ◇ X0) ◇ (sK1 ◇ X0)) ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))))) ◇ sK1) := superpose eq83 eq9412
  have eq9467 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK1 ◇ (((sK2 ◇ X0) ◇ (sK1 ◇ X0)) ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))))) ◇ sK2) := superpose eq846 eq9441
  have eq9484 (X0 : G) : sK0 ≠ ((sK1 ◇ (((sK2 ◇ X0) ◇ X0) ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))))) ◇ sK2) := superpose eq1338 eq9467
  have eq9494 (X0 : G) : sK0 ≠ ((sK2 ◇ X0) ◇ ((sK2 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))))) ◇ sK1)) := superpose eq4693 eq9484
  have eq9502 (X0 : G) : sK0 ≠ (X0 ◇ ((sK2 ◇ (sK2 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))))) ◇ sK1)) := superpose eq792 eq9494
  have eq9510 (X0 : G) : sK0 ≠ (X0 ◇ ((sK1 ◇ (sK2 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))))) ◇ sK2)) := superpose eq846 eq9502
  have eq9518 (X0 : G) : sK0 ≠ (X0 ◇ ((sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))))) ◇ sK2)) := superpose eq436 eq9510
  have eq9526 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ ((sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))))) ◇ sK1))) := superpose eq4693 eq9518
  have eq9534 (X0 : G) : sK0 ≠ (X0 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))))) ◇ sK2)) := superpose eq97 eq9526
  have eq9542 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))) ◇ sK2) := superpose eq1338 eq9534
  have eq9550 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))))))) ◇ sK2)) := superpose eq85 eq9542
  have eq9558 : sK0 ≠ (sK1 ◇ ((((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))) ◇ sK1)) := superpose eq50 eq9550
  have eq9566 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq405 eq9558
  have eq9574 : sK0 ≠ sK0 := superpose eq57 eq9566
  subsumption eq9574 rfl

theorem Equation3211_termDefinableFrom_Equation3182 :
    Law3211.TermDefinableFrom Law3182 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op x (M.op y x))⟩, ?_, ?_⟩
  · rw [@Law3211.models_iff]
    exact @law3211_of_law3182 G M (Law3182.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 1) (Term.var 0)))), rfl⟩

/-- Equation 3185 `x = (((y ◇ z) ◇ x) ◇ z) ◇ y` is term-definable from equation 3128 `x = (((y ◇ x) ◇ z) ◇ y) ◇ z`,
via the term `x □ y := x ◇ (y ◇ (x ◇ x))`. -/
private theorem law3185_of_law3128 [Magma G] (h : Equation3128 G) :
    ∀ x y z : G, x = (((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y)))))) ◇ (z ◇ (((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y)))))) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y))))))))) ◇ (y ◇ ((((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y)))))) ◇ (z ◇ (((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y)))))) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y))))))))) ◇ (((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y)))))) ◇ (z ◇ (((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y)))))) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y))))))))))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))) ◇ (sK2 ◇ (((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))))))) ◇ (sK1 ◇ ((((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))) ◇ (sK2 ◇ (((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))))))) ◇ (((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))) ◇ (sK2 ◇ (((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))))))))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = X1 := superpose eq8 eq8
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq8 eq8
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq12 eq11
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X2 := superpose eq12 eq8
  have eq28 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X2 := superpose eq12 eq23
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq28
  have eq40 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq8 eq13
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq12 eq13
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2)))) = X2 := superpose eq13 eq8
  have eq54 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq12 eq40
  have eq190 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := superpose eq46 eq36
  have eq646 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = ((X1 ◇ X3) ◇ (X2 ◇ X0)) := superpose eq50 eq36
  have eq1481 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X1 ◇ X4)) = ((X3 ◇ X4) ◇ (X5 ◇ ((X3 ◇ X5) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq54 eq50
  have eq1490 (X0 : G) : sK0 ≠ ((X0 ◇ ((X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))))) ◇ sK2)) ◇ (sK1 ◇ ((X0 ◇ ((X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))))) ◇ sK2)) ◇ (X0 ◇ ((X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))))) ◇ sK2))))) := superpose eq54 eq9
  have eq1539 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X2) ◇ X1) = ((X3 ◇ X4) ◇ (X5 ◇ ((X3 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq54 eq50
  have eq1585 (X0 : G) : sK0 ≠ ((X0 ◇ sK1) ◇ (((X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))))) ◇ sK2) ◇ ((X0 ◇ ((X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))))) ◇ sK2)) ◇ (X0 ◇ ((X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))))) ◇ sK2))))) := superpose eq646 eq1490
  have eq1655 : sK0 ≠ (sK2 ◇ (((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))) ◇ sK1)) := superpose eq1481 eq1585
  have eq1673 : sK0 ≠ (sK2 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))))) := superpose eq190 eq1655
  have eq1680 : sK0 ≠ (sK2 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))))))) := superpose eq646 eq1673
  have eq1686 : sK0 ≠ (sK2 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK2))) := superpose eq1539 eq1680
  have eq1690 : sK0 ≠ sK0 := superpose eq13 eq1686
  subsumption eq1690 rfl

theorem Equation3185_termDefinableFrom_Equation3128 :
    Law3185.TermDefinableFrom Law3128 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op y (M.op x x))⟩, ?_, ?_⟩
  · rw [@Law3185.models_iff]
    exact @law3185_of_law3128 G M (Law3128.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (tm (Term.var 0) (Term.var 0)))), rfl⟩

/-- Equation 3195 `x = (((y ◇ z) ◇ y) ◇ x) ◇ z` is term-definable from equation 2576 `x = (y ◇ ((z ◇ x) ◇ z)) ◇ y`,
via the term `x □ y := ((x ◇ x) ◇ x) ◇ y`. -/
private theorem law3195_of_law2576 [Magma G] (h : Equation2576 G) :
    ∀ x y z : G, x = (((((((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y)) ◇ ((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y)) ◇ x) ◇ (((((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y)) ◇ ((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y)) ◇ x)) ◇ (((((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y)) ◇ ((((((y ◇ y) ◇ y) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ y)) ◇ x)) ◇ z := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((((((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1) ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ sK0) ◇ (((((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1) ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ sK0)) ◇ (((((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1) ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ X1) := superpose eq8 eq8
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ X1)) := superpose eq11 eq11
  have eq36 (X0 : G) : sK0 ≠ (((X0 ◇ (((((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1) ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ sK0)) ◇ X0) ◇ sK2) := superpose eq11 eq9
  have eq71 (X0 X1 : G) : sK0 ≠ (((X1 ◇ (((X0 ◇ ((((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ sK1)) ◇ X0) ◇ sK0)) ◇ X1) ◇ sK2) := superpose eq11 eq36
  have eq110 (X0 X1 X2 : G) : sK0 ≠ (((X1 ◇ (((X2 ◇ (((X0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) ◇ X0) ◇ sK1)) ◇ X2) ◇ sK0)) ◇ X1) ◇ sK2) := superpose eq11 eq71
  have eq137 (X0 X1 X2 X3 : G) : sK0 ≠ (((X1 ◇ (((X2 ◇ ((X0 ◇ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK2) ◇ ((X3 ◇ X0) ◇ X3))) ◇ sK1)) ◇ X2) ◇ sK0)) ◇ X1) ◇ sK2) := superpose eq8 eq110
  have eq230 (X0 X1 : G) : sK0 ≠ (((X0 ◇ (((X1 ◇ sK2) ◇ X1) ◇ sK0)) ◇ X0) ◇ sK2) := superpose eq8 eq137
  have eq556 (X0 X1 X2 : G) : sK0 ≠ ((((X0 ◇ ((X1 ◇ sK2) ◇ X1)) ◇ X0) ◇ ((X2 ◇ sK0) ◇ X2)) ◇ sK2) := superpose eq21 eq230
  have eq586 (X2 : G) : sK0 ≠ ((sK2 ◇ ((X2 ◇ sK0) ◇ X2)) ◇ sK2) := superpose eq8 eq556
  have eq610 : sK0 ≠ sK0 := superpose eq8 eq586
  subsumption eq610 rfl

theorem Equation3195_termDefinableFrom_Equation2576 :
    Law3195.TermDefinableFrom Law2576 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op (M.op x x) x) y⟩, ?_, ?_⟩
  · rw [@Law3195.models_iff]
    exact @law3195_of_law2576 G M (Law2576.models_iff.mp hGL)
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩

/-- Equation 3128 `x = (((y ◇ x) ◇ z) ◇ y) ◇ z` is term-definable from equation 3185 `x = (((y ◇ z) ◇ x) ◇ z) ◇ y`,
via the term `x □ y := (x ◇ x) ◇ (y ◇ x)`. -/
private theorem law3128_of_law3185 [Magma G] (h : Equation3185 G) :
    ∀ x y z : G, x = (((((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ ((((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y))))))) ◇ (z ◇ ((((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (z ◇ ((y ◇ y) ◇ (x ◇ y))))))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))) ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ◇ ((((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))) ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))))) ◇ (sK2 ◇ ((((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))) ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))))))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X3 := superpose eq8 eq8
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq8 eq8
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq8 eq8
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq12 eq8
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X2) ◇ X1) := superpose eq12 eq8
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X2 := superpose eq12 eq11
  have eq20 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X3) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq8 eq11
  have eq28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ (X2 ◇ X3)) := superpose eq15 eq20
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X2 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq14 eq14
  have eq59 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X0 ◇ X2) ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) := superpose eq12 eq10
  have eq108 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X0 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq15 eq59
  have eq142 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((X3 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq15 eq15
  have eq220 (X0 X1 X2 X3 : G) : ((((X2 ◇ X1) ◇ X3) ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X2)) := superpose eq8 eq19
  have eq223 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X3 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq14 eq19
  have eq264 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X3 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3)) := superpose eq142 eq220
  have eq370 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3))) := superpose eq10 eq18
  have eq1081 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ (X4 ◇ X2)) = ((X3 ◇ X4) ◇ (X0 ◇ X1)) := superpose eq39 eq28
  have eq1150 (X0 : G) : sK0 ≠ ((X0 ◇ sK2) ◇ (((((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))) ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ◇ X0)) := superpose eq28 eq9
  have eq1233 : sK0 ≠ ((sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))) ◇ (sK2 ◇ (((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))))) := superpose eq223 eq1150
  have eq1279 (X0 X1 X3 X4 : G) : ((X3 ◇ X4) ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ (X4 ◇ X1)) := superpose eq264 eq1081
  have eq1358 : sK0 ≠ ((((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ sK2) ◇ sK1) := superpose eq370 eq1233
  have eq1426 : sK0 ≠ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))) := superpose eq142 eq1358
  have eq1458 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))) := superpose eq1279 eq1426
  have eq1480 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose eq108 eq1458
  have eq1499 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose eq142 eq1480
  have eq1511 : sK0 ≠ sK0 := superpose eq11 eq1499
  subsumption eq1511 rfl

theorem Equation3128_termDefinableFrom_Equation3185 :
    Law3128.TermDefinableFrom Law3185 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law3128.models_iff]
    exact @law3128_of_law3185 G M (Law3185.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩

/-- Equation 1888 `x = (y ◇ (x ◇ x)) ◇ (y ◇ y)` is term-definable from equation 281 `x = ((y ◇ y) ◇ x) ◇ y`,
via the term `x □ y := (x ◇ x) ◇ (y ◇ y)`. -/
private theorem law1888_of_law281 [Magma G] (h : Equation281 G) :
    ∀ x y : G, x = (((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK1 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) ◇ ((sK1 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8
  have eq14 : sK0 ≠ ((((sK1 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) ◇ ((sK1 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) ◇ (sK1 ◇ sK1)) := superpose eq10 eq9
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8
  have eq16 : sK0 ≠ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := superpose eq10 eq14
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq15 eq15
  have eq37 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq21 eq21
  have eq40 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq37
  have eq46 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq40 eq16
  have eq52 : sK0 ≠ sK0 := superpose eq10 eq46
  subsumption eq52 rfl

theorem Equation1888_termDefinableFrom_Equation281 :
    Law1888.TermDefinableFrom Law281 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op y y)⟩, ?_, ?_⟩
  · rw [@Law1888.models_iff]
    exact @law1888_of_law281 G M (Law281.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), rfl⟩

/-- Equation 3195 `x = (((y ◇ z) ◇ y) ◇ x) ◇ z` is term-definable from equation 3106 `x = (((y ◇ x) ◇ x) ◇ y) ◇ y`,
via the term `x □ y := (x ◇ y) ◇ y`. -/
private theorem law3195_of_law3106 [Magma G] (h : Equation3106 G) :
    ∀ x y z : G, x = (((((((y ◇ z) ◇ z) ◇ y) ◇ y) ◇ x) ◇ x) ◇ z) ◇ z := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((((((sK1 ◇ sK2) ◇ sK2) ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 : sK0 ≠ ((((sK2 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq8 eq9
  have eq13 : sK0 ≠ sK0 := superpose eq8 eq12
  subsumption eq13 rfl

theorem Equation3195_termDefinableFrom_Equation3106 :
    Law3195.TermDefinableFrom Law3106 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x y) y⟩, ?_, ?_⟩
  · rw [@Law3195.models_iff]
    exact @law3195_of_law3106 G M (Law3106.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), rfl⟩

/-- Equation 4608 `(x ◇ x) ◇ y = (y ◇ y) ◇ x` is term-definable from equation 4007 `x ◇ y = (z ◇ (y ◇ x)) ◇ z`,
via the term `x □ y := (x ◇ x) ◇ ((y ◇ y) ◇ (y ◇ y))`. -/
private theorem law4608_of_law4007 [Magma G] (h : Equation4007 G) :
    ∀ x y : G, (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ ((y ◇ y) ◇ (y ◇ y)) = (((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ y))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ y)))) ◇ ((x ◇ x) ◇ (x ◇ x)) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq9 : ((((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ≠ ((((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X0))) = ((X3 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq8 eq8
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ ((X3 ◇ X2) ◇ (X1 ◇ X0))) := superpose eq8 eq8
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq8 eq10
  have eq17 : ((((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose eq12 eq9
  have eq18 : (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := superpose eq11 eq17
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := superpose eq11 eq8
  have eq139 : (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := superpose eq34 eq18
  subsumption eq139 rfl

theorem Equation4608_termDefinableFrom_Equation4007 :
    Law4608.TermDefinableFrom Law4007 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op (M.op y y) (M.op y y))⟩, ?_, ?_⟩
  · rw [@Law4608.models_iff]
    exact @law4608_of_law4007 G M (Law4007.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (tm (Term.var 1) (Term.var 1)) (tm (Term.var 1) (Term.var 1)))), rfl⟩

/-- Equation 4162 `x ◇ y = ((y ◇ x) ◇ z) ◇ z` is term-definable from equation 4216 `x ◇ y = ((z ◇ y) ◇ z) ◇ x`,
via the term `x □ y := (x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))`. -/
private theorem law4162_of_law4216 [Magma G] (h : Equation4216 G) :
    ∀ x y z : G, (x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)) = (((((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z))) ◇ z) ◇ ((((((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z))) ◇ z) ◇ (((((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))) ◇ z))) ◇ z)) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((((((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2) ◇ ((((((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2) ◇ (((((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2) := superpose eq8 eq8
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq8 eq11
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X1 ◇ X3) ◇ X3)) := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X2) := superpose eq8 eq11
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq11
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq15 eq13
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq15 eq12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq8 eq18
  have eq21 (X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq8 eq19
  have eq30 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq10 eq10
  have eq49 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq15 eq30
  have eq60 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ X1) ◇ X2) := superpose eq21 eq49
  have eq69 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X1 ◇ (((X4 ◇ X1) ◇ X4) ◇ X3)) ◇ X2) := superpose eq15 eq60
  have eq75 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X3 ◇ X1)) ◇ X2) := superpose eq8 eq69
  have eq192 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ X2) ◇ X3) := superpose eq15 eq15
  have eq218 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := superpose eq15 eq14
  have eq219 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq15 eq14
  have eq225 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2) ◇ ((((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2) ◇ (((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2))) := superpose eq15 eq9
  have eq230 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) := superpose eq15 eq8
  have eq234 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X1 ◇ X0) ◇ (X2 ◇ X3)) := superpose eq15 eq14
  have eq242 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK2 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) ◇ ((((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2) ◇ (((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2))) := superpose eq234 eq225
  have eq274 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK2 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) ◇ ((((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2) ◇ (sK2 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))))) := superpose eq15 eq242
  have eq297 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK2 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) ◇ ((sK2 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) ◇ (((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ sK2))) := superpose eq218 eq274
  have eq312 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK2 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) ◇ ((sK2 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) ◇ (sK2 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))))) := superpose eq218 eq297
  have eq323 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)) ◇ ((sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) := superpose eq20 eq312
  have eq331 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ (((sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)))) := superpose eq75 eq323
  have eq339 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ (((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ sK2) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) := superpose eq192 eq331
  have eq347 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((((((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2) ◇ sK2) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2))) ◇ (sK1 ◇ sK0)) := superpose eq230 eq339
  have eq355 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) := superpose eq192 eq347
  have eq363 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) := superpose eq219 eq355
  have eq371 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))))) := superpose eq75 eq363
  have eq379 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK0 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) := superpose eq218 eq371
  have eq387 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)) ◇ (sK1 ◇ sK0))) := superpose eq230 eq379
  have eq395 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) := superpose eq218 eq387
  have eq403 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) ◇ sK2)))) := superpose eq219 eq395
  have eq411 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))))) := superpose eq21 eq403
  have eq419 : ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := superpose eq21 eq411
  subsumption eq419 rfl

theorem Equation4162_termDefinableFrom_Equation4216 :
    Law4162.TermDefinableFrom Law4216 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x y) (M.op (M.op x y) (M.op x y))⟩, ?_, ?_⟩
  · rw [@Law4162.models_iff]
    exact @law4162_of_law4216 G M (Law4216.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (Term.var 1)))), rfl⟩

/-- Equation 4450 `x ◇ (y ◇ x) = (y ◇ z) ◇ z` is term-definable from equation 4216 `x ◇ y = ((z ◇ y) ◇ z) ◇ x`,
via the term `x □ y := (x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))`. -/
private theorem law4450_of_law4216 [Magma G] (h : Equation4216 G) :
    ∀ x y z : G, (x ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ ((x ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (x ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))))) = (((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z) ◇ ((((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z) ◇ (((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z)) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2) := superpose eq8 eq8
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq8 eq11
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X1 ◇ X3) ◇ X3)) := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X2) := superpose eq8 eq11
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq11
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq15 eq13
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq15 eq12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq8 eq18
  have eq21 (X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq8 eq19
  have eq30 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq10 eq10
  have eq49 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq15 eq30
  have eq60 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ X1) ◇ X2) := superpose eq21 eq49
  have eq69 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X1 ◇ (((X4 ◇ X1) ◇ X4) ◇ X3)) ◇ X2) := superpose eq15 eq60
  have eq75 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X3 ◇ X1)) ◇ X2) := superpose eq8 eq69
  have eq111 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ ((sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) ◇ ((sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))))) := superpose eq14 eq9
  have eq117 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq20 eq111
  have eq136 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ (((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1) := superpose eq75 eq117
  have eq142 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq15 eq136
  have eq147 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK1)) := superpose eq75 eq142
  have eq148 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2))) := superpose eq15 eq147
  have eq149 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := superpose eq15 eq148
  have eq150 : ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq20 eq149
  have eq151 : (sK1 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq20 eq150
  have eq152 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := superpose eq75 eq151
  have eq153 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq15 eq152
  have eq154 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := superpose eq75 eq153
  have eq155 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := superpose eq15 eq154
  have eq156 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq15 eq155
  have eq157 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq20 eq156
  subsumption eq157 rfl

theorem Equation4450_termDefinableFrom_Equation4216 :
    Law4450.TermDefinableFrom Law4216 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x y) (M.op (M.op x y) (M.op x y))⟩, ?_, ?_⟩
  · rw [@Law4450.models_iff]
    exact @law4450_of_law4216 G M (Law4216.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (Term.var 1)))), rfl⟩

/-- Equation 4216 `x ◇ y = ((z ◇ y) ◇ z) ◇ x` is term-definable from equation 4007 `x ◇ y = (z ◇ (y ◇ x)) ◇ z`,
via the term `x □ y := ((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ y))`. -/
private theorem law4216_of_law4007 [Magma G] (h : Equation4007 G) :
    ∀ x y z : G, ((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ y)) = ((((((((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y))) ◇ (((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y)))) ◇ (((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y)))) ◇ (z ◇ (z ◇ z))) ◇ ((((((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y))) ◇ (((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y)))) ◇ (((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y)))) ◇ (z ◇ (z ◇ z)))) ◇ ((((((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y))) ◇ (((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y)))) ◇ (((z ◇ z) ◇ z) ◇ (y ◇ (y ◇ y)))) ◇ (z ◇ (z ◇ z)))) ◇ (x ◇ (x ◇ x)) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq9 : (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) ≠ (((((((((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ ((((((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ ((((((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ ((X3 ◇ X2) ◇ (X1 ◇ X0))) := superpose eq8 eq8
  have eq14 : (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) ≠ (((sK2 ◇ (sK2 ◇ sK2)) ◇ (((((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq8 eq9
  have eq15 : (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) ≠ (((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq8 eq14
  have eq17 : (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq15
  have eq37 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := superpose eq11 eq8
  have eq151 : (((sK1 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq37 eq17
  subsumption eq151 rfl

theorem Equation4216_termDefinableFrom_Equation4007 :
    Law4216.TermDefinableFrom Law4007 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op (M.op x x) x) (M.op y (M.op y y))⟩, ?_, ?_⟩
  · rw [@Law4216.models_iff]
    exact @law4216_of_law4007 G M (Law4007.models_iff.mp hGL)
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (tm (Term.var 1) (tm (Term.var 1) (Term.var 1)))), rfl⟩

/-- Equation 4636 `(x ◇ y) ◇ x = (y ◇ x) ◇ y` is term-definable from equation 3973 `x ◇ y = (y ◇ (z ◇ x)) ◇ z`,
via the term `x □ y := x ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ y)`. -/
private theorem law4636_of_law3973 [Magma G] (h : Equation3973 G) :
    ∀ x y : G, (x ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ y)) ◇ (((x ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ y)) ◇ (((x ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ y)) ◇ x) ◇ (x ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ y)))) ◇ x) = (y ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ x)) ◇ (((y ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ x)) ◇ (((y ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ x)) ◇ y) ◇ (y ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ x)))) ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0)) ◇ (((sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0)) ◇ (((sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0)) ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0)))) ◇ sK1)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq8 eq8
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X0))) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq8
  have eq14 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X4))) = ((X0 ◇ X1) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X4))) := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X0))) = ((X0 ◇ X1) ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq8 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq10 eq8
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X4) = ((X4 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X2))) := superpose eq10 eq8
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X0 ◇ X2)) ◇ X4) ◇ X1) = ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq10 eq11
  have eq38 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq11 eq8
  have eq41 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) = ((X4 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) := superpose eq11 eq8
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) = ((X0 ◇ X1) ◇ (X4 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X5))) := superpose eq10 eq20
  have eq53 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X1 ◇ ((X2 ◇ X5) ◇ X0))) = ((X3 ◇ X5) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq20
  have eq55 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X0))) ◇ X4) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq8 eq20
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X1) ◇ X0) := superpose eq20 eq10
  have eq71 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X4 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X5))) = ((X3 ◇ X1) ◇ (X4 ◇ (X2 ◇ X5))) := superpose eq29 eq47
  have eq89 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = (((X2 ◇ X3) ◇ (X1 ◇ (X4 ◇ X0))) ◇ X3) := superpose eq8 eq38
  have eq90 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (X1 ◇ (X4 ◇ X5))) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ (X5 ◇ (X0 ◇ X4))) := superpose eq10 eq38
  have eq96 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = ((((X2 ◇ (X0 ◇ X3)) ◇ X4) ◇ X1) ◇ X4) := superpose eq10 eq38
  have eq121 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X1 ◇ (X3 ◇ X0)) := superpose eq38 eq8
  have eq130 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X5) = ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (X4 ◇ (X3 ◇ X5))) := superpose eq38 eq20
  have eq133 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X2 ◇ (X4 ◇ X5)) ◇ X0)) = ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (X5 ◇ (X3 ◇ X4))) := superpose eq38 eq10
  have eq137 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X2 ◇ (X4 ◇ X5)) ◇ X0)) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X5 ◇ (X3 ◇ X4))) := superpose eq59 eq133
  have eq140 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X5) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X3 ◇ X5))) := superpose eq59 eq130
  have eq148 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq59 eq121
  have eq171 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = ((X4 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) := superpose eq59 eq96
  have eq176 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (X1 ◇ (X4 ◇ X5))) ◇ X3) = (X0 ◇ (X2 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X1)))) := superpose eq15 eq90
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = ((X3 ◇ (X1 ◇ (X4 ◇ X0))) ◇ (X2 ◇ X3)) := superpose eq59 eq89
  have eq197 (X0 X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X5) = (X3 ◇ ((X2 ◇ (X5 ◇ X4)) ◇ X0)) := superpose eq137 eq140
  have eq213 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = ((X0 ◇ X3) ◇ (X1 ◇ X2)) := superpose eq148 eq171
  have eq217 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X1)))) = ((X3 ◇ (X1 ◇ (X4 ◇ X5))) ◇ (X2 ◇ X3)) := superpose eq59 eq176
  have eq234 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X2 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X1)))) = (((X5 ◇ X1) ◇ X2) ◇ X4) := superpose eq177 eq217
  have eq259 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((X3 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq59 eq59
  have eq291 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ ((sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)) ◇ (((sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)) ◇ (((sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)))) ◇ sK1)) := superpose eq59 eq9
  have eq308 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ (X2 ◇ X1)) ◇ X4) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) := superpose eq59 eq38
  have eq309 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ X1) = ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq59 eq20
  have eq312 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) := superpose eq59 eq8
  have eq315 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = ((X0 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq59 eq312
  have eq318 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ (X2 ◇ X1)) ◇ X4) = ((X0 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq59 eq308
  have eq332 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ ((((sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)))) := superpose eq148 eq291
  have eq369 (X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ X2)) = (((X3 ◇ X4) ◇ (X2 ◇ X1)) ◇ X4) := superpose eq315 eq318
  have eq376 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ ((((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)) ◇ sK1)) := superpose eq21 eq332
  have eq388 (X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ X2)) = ((X4 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq59 eq369
  have eq391 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ (((sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ sK1)) := superpose eq197 eq376
  have eq397 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1)))) ◇ sK1)) := superpose eq259 eq391
  have eq401 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)))) ◇ sK1)) := superpose eq15 eq397
  have eq405 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1)))) := superpose eq55 eq401
  have eq409 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)))) := superpose eq53 eq405
  have eq413 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK1)) := superpose eq11 eq409
  have eq417 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK1)) := superpose eq20 eq413
  have eq421 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0)) := superpose eq41 eq417
  have eq425 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1)) := superpose eq41 eq421
  have eq429 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) := superpose eq59 eq425
  have eq433 : ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) := superpose eq59 eq429
  have eq437 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)))) := superpose eq388 eq433
  have eq441 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) := superpose eq41 eq437
  have eq445 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ ((((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := superpose eq15 eq441
  have eq449 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0)))) := superpose eq15 eq445
  have eq453 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK1 ◇ (((sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK0) ◇ sK0)) ◇ sK1)) := superpose eq309 eq449
  have eq457 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ sK0)) := superpose eq41 eq453
  have eq461 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (((sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ sK1) ◇ sK0)) ◇ sK1)) := superpose eq41 eq457
  have eq465 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ sK1)) := superpose eq59 eq461
  have eq469 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ sK1)) := superpose eq53 eq465
  have eq473 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ sK1)) := superpose eq14 eq469
  have eq477 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ sK1)) := superpose eq15 eq473
  have eq481 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ sK1)) := superpose eq53 eq477
  have eq485 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ sK1)) := superpose eq15 eq481
  have eq489 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ sK1)) := superpose eq71 eq485
  have eq493 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ sK1)) := superpose eq20 eq489
  have eq497 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1) ◇ sK1)))) ◇ sK1)) := superpose eq53 eq493
  have eq501 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ sK1)) := superpose eq59 eq497
  have eq505 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)))))) ◇ sK1)) := superpose eq53 eq501
  have eq509 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)))) ◇ sK1)) := superpose eq11 eq505
  have eq513 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ (((((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1)) := superpose eq234 eq509
  have eq517 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0))) ◇ sK1)) ◇ sK1)) := superpose eq41 eq513
  have eq521 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)))) := superpose eq41 eq517
  have eq525 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) ◇ (sK1 ◇ sK0)) := superpose eq11 eq521
  have eq529 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0)) := superpose eq213 eq525
  have eq533 : (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) := superpose eq41 eq529
  subsumption eq533 rfl

theorem Equation4636_termDefinableFrom_Equation3973 :
    Law4636.TermDefinableFrom Law3973 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op (M.op x (M.op (M.op x y) x)) y)⟩, ?_, ?_⟩
  · rw [@Law4636.models_iff]
    exact @law4636_of_law3973 G M (Law3973.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))) (Term.var 1))), rfl⟩

/-- Equation 4608 `(x ◇ x) ◇ y = (y ◇ y) ◇ x` is term-definable from equation 3973 `x ◇ y = (y ◇ (z ◇ x)) ◇ z`,
via the term `x □ y := (y ◇ (x ◇ x)) ◇ y`. -/
private theorem law4608_of_law3973 [Magma G] (h : Equation3973 G) :
    ∀ x y : G, (y ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ y = (x ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇ x := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq9 : ((sK1 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) ◇ sK1) ≠ ((sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq8 eq8
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X0))) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq8
  have eq17 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X0))) = ((X0 ◇ X1) ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq8 eq10
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq10 eq8
  have eq31 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X0 ◇ X2)) ◇ X4) ◇ X1) = ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq10 eq11
  have eq39 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq11 eq8
  have eq42 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) = ((X4 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) := superpose eq11 eq8
  have eq52 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = ((X2 ◇ (X1 ◇ (X4 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq8 eq22
  have eq53 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X5))) = ((X2 ◇ (X1 ◇ (X5 ◇ X4))) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq10 eq22
  have eq61 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X1) ◇ X0) := superpose eq22 eq10
  have eq72 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X4))) := superpose eq53 eq52
  have eq120 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) := superpose eq61 eq8
  have eq122 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = ((X0 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq61 eq120
  have eq170 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ (X2 ◇ X3)) ◇ X4) = ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) := superpose eq39 eq39
  have eq183 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = (((X3 ◇ X4) ◇ (X2 ◇ X1)) ◇ X4) := superpose eq61 eq39
  have eq221 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) := superpose eq39 eq8
  have eq256 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq61 eq221
  have eq291 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = ((X4 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq61 eq183
  have eq304 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ (X2 ◇ X3)) ◇ X4) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq61 eq170
  have eq340 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X4 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq61 eq291
  have eq345 (X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X2)) = (((X3 ◇ X4) ◇ (X2 ◇ X3)) ◇ X4) := superpose eq122 eq304
  have eq365 (X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ X2)) = ((X4 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq122 eq340
  have eq369 (X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X2)) = ((X4 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) := superpose eq61 eq345
  have eq387 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ X2)) := superpose eq365 eq369
  have eq467 (X0 : G) : ((sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK0) ≠ ((sK1 ◇ (((X0 ◇ (X0 ◇ sK0)) ◇ sK0) ◇ ((X0 ◇ (X0 ◇ sK0)) ◇ sK0))) ◇ sK1) := superpose eq387 eq9
  have eq468 (X0 : G) : ((sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ ((((X0 ◇ (X0 ◇ sK0)) ◇ sK0) ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK0)))) ◇ sK1) := superpose eq42 eq467
  have eq530 (X0 : G) : ((sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ (sK1 ◇ ((sK0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ sK0)) ◇ sK0))))) ◇ sK1) := superpose eq17 eq468
  have eq550 (X0 : G) : ((sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ ((((X0 ◇ (X0 ◇ sK0)) ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1) := superpose eq11 eq530
  have eq560 (X0 : G) : ((sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((X0 ◇ (X0 ◇ sK0)) ◇ sK0))) ◇ sK1) := superpose eq61 eq550
  have eq562 (X0 : G) : ((sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ ((X0 ◇ sK0) ◇ (sK1 ◇ X0))) ◇ sK1) := superpose eq256 eq560
  have eq564 (X0 : G) : ((sK0 ◇ ((X0 ◇ sK0) ◇ (sK1 ◇ X0))) ◇ sK1) ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))))) ◇ sK0) := superpose eq31 eq562
  have eq566 (X0 : G) : ((sK0 ◇ ((X0 ◇ sK0) ◇ (sK1 ◇ X0))) ◇ sK1) ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK0) := superpose eq22 eq564
  have eq568 (X0 : G) : ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ ((X0 ◇ sK0) ◇ (sK1 ◇ X0))) ◇ sK1) := superpose eq122 eq566
  have eq922 (X0 X1 : G) : ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ (((sK1 ◇ X1) ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ sK1) := superpose eq387 eq568
  have eq925 (X1 : G) : ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ (((sK1 ◇ X1) ◇ sK0) ◇ X1)) ◇ sK1) := superpose eq72 eq922
  have eq934 (X1 : G) : ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ sK0) ≠ ((sK0 ◇ ((X1 ◇ sK1) ◇ (sK1 ◇ X1))) ◇ sK0) := superpose eq42 eq925
  subsumption eq934 rfl

theorem Equation4608_termDefinableFrom_Equation3973 :
    Law4608.TermDefinableFrom Law3973 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op y (M.op x x)) y⟩, ?_, ?_⟩
  · rw [@Law4608.models_iff]
    exact @law4608_of_law3973 G M (Law3973.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), rfl⟩

/-- Equation 4640 `(x ◇ y) ◇ x = (y ◇ z) ◇ z` is term-definable from equation 4216 `x ◇ y = ((z ◇ y) ◇ z) ◇ x`,
via the term `x □ y := (x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))`. -/
private theorem law4640_of_law4216 [Magma G] (h : Equation4216 G) :
    ∀ x y z : G, (((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ x) ◇ ((((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ x) ◇ (((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ x)) = (((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z) ◇ ((((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z) ◇ (((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z)) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq9 : ((((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ sK0) ◇ ((((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ sK0))) ≠ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2) := superpose eq8 eq8
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq8 eq11
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X1 ◇ X3) ◇ X3)) := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X2) := superpose eq8 eq11
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq11
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq15 eq13
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq15 eq12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq8 eq18
  have eq21 (X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq8 eq19
  have eq30 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq10 eq10
  have eq49 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq15 eq30
  have eq60 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ X1) ◇ X2) := superpose eq21 eq49
  have eq69 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X1 ◇ (((X4 ◇ X1) ◇ X4) ◇ X3)) ◇ X2) := superpose eq15 eq60
  have eq75 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X3 ◇ X1)) ◇ X2) := superpose eq8 eq69
  have eq105 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq8
  have eq111 : ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := superpose eq14 eq9
  have eq117 : ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq20 eq111
  have eq136 : ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := superpose eq105 eq117
  have eq142 : ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq15 eq136
  have eq147 : ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := superpose eq105 eq142
  have eq148 : ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := superpose eq15 eq147
  have eq149 : ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq15 eq148
  have eq150 : ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq21 eq149
  have eq151 : (sK1 ◇ (sK1 ◇ sK1)) ≠ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))))) := superpose eq15 eq150
  have eq152 : (sK1 ◇ (sK1 ◇ sK1)) ≠ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))))) := superpose eq15 eq151
  have eq153 : (sK1 ◇ (sK1 ◇ sK1)) ≠ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq20 eq152
  have eq154 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))))) := superpose eq15 eq153
  have eq155 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2))) := superpose eq20 eq154
  have eq156 : (sK1 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq15 eq155
  have eq157 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1) := superpose eq75 eq156
  have eq158 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq15 eq157
  have eq159 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK1)) := superpose eq75 eq158
  have eq160 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2))) := superpose eq15 eq159
  have eq161 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := superpose eq15 eq160
  have eq162 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq20 eq161
  subsumption eq162 rfl

theorem Equation4640_termDefinableFrom_Equation4216 :
    Law4640.TermDefinableFrom Law4216 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x y) (M.op (M.op x y) (M.op x y))⟩, ?_, ?_⟩
  · rw [@Law4640.models_iff]
    exact @law4640_of_law4216 G M (Law4216.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (Term.var 1)))), rfl⟩

/-- Equation 2707 `x = ((y ◇ x) ◇ (y ◇ x)) ◇ y` is term-definable from equation 281 `x = ((y ◇ y) ◇ x) ◇ y`,
via the term `x □ y := (x ◇ x) ◇ (y ◇ y)`. -/
private theorem law2707_of_law281 [Magma G] (h : Equation281 G) :
    ∀ x y : G, x = (((((y ◇ y) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (x ◇ x)))) ◇ ((((y ◇ y) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (x ◇ x))))) ◇ (y ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)))) ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))))) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8
  have eq12 : sK0 ≠ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := superpose eq10 eq9
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq13 eq13
  have eq25 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq15 eq15
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq25
  have eq34 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq28 eq12
  have eq40 : sK0 ≠ sK0 := superpose eq10 eq34
  subsumption eq40 rfl

theorem Equation2707_termDefinableFrom_Equation281 :
    Law2707.TermDefinableFrom Law281 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op y y)⟩, ?_, ?_⟩
  · rw [@Law2707.models_iff]
    exact @law2707_of_law281 G M (Law281.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), rfl⟩

/-- Equation 4458 `x ◇ (y ◇ x) = (z ◇ y) ◇ z` is term-definable from equation 3685 `x ◇ x = (y ◇ y) ◇ (x ◇ y)`,
via the term `x □ y := (x ◇ x) ◇ (y ◇ y)`. -/
private theorem law4458_of_law3685 [Magma G] (h : Equation3685 G) :
    ∀ x y z : G, (x ◇ x) ◇ (((y ◇ y) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (x ◇ x))) = (((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (z ◇ z) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)))) ≠ ((((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq8 eq8
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) := superpose eq8 eq8
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq8 eq8
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq8 eq8
  have eq17 (X0 : G) : ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)))) ≠ (((X0 ◇ X0) ◇ (((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) ◇ X0)) ◇ (sK2 ◇ sK2)) := superpose eq8 eq9
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq8 eq15
  have eq42 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq13 eq8
  have eq223 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)))) ≠ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X1))) ◇ (sK2 ◇ sK2)) := superpose eq10 eq17
  have eq279 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X3)))) := superpose eq12 eq12
  have eq345 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X3)))) := superpose eq18 eq279
  have eq375 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq12 eq18
  have eq386 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq18 eq13
  have eq397 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq8 eq386
  have eq716 (X0 X1 X2 : G) : ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)))) ≠ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (sK2 ◇ sK2)) := superpose eq8 eq223
  have eq730 (X0 X1 X2 : G) : ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)))) ≠ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (sK2 ◇ sK2)) := superpose eq397 eq716
  have eq754 (X0 X1 X2 : G) : ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) ≠ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (sK2 ◇ sK2)) := superpose eq397 eq730
  have eq775 (X0 X1 X2 : G) : (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ≠ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (sK2 ◇ sK2)) := superpose eq345 eq754
  have eq796 (X0 X1 X2 : G) : ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ≠ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (sK2 ◇ sK2)) := superpose eq8 eq775
  have eq817 (X0 X1 X2 : G) : (sK1 ◇ sK1) ≠ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (sK2 ◇ sK2)) := superpose eq8 eq796
  have eq1681 (X0 : G) : (sK1 ◇ sK1) ≠ ((((X0 ◇ X0) ◇ ((sK2 ◇ sK1) ◇ X0)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK2)) := superpose eq42 eq817
  have eq1713 : (sK1 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq375 eq1681
  subsumption eq1713 rfl

theorem Equation4458_termDefinableFrom_Equation3685 :
    Law4458.TermDefinableFrom Law3685 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op y y)⟩, ?_, ?_⟩
  · rw [@Law4458.models_iff]
    exact @law4458_of_law3685 G M (Law3685.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), rfl⟩

/-- Equation 3994 `x ◇ y = (z ◇ (x ◇ y)) ◇ z` is term-definable from equation 4446 `x ◇ (y ◇ x) = (y ◇ y) ◇ y`,
via the term `x □ y := x ◇ ((x ◇ y) ◇ x)`. -/
private theorem law3994_of_law4446 [Magma G] (h : Equation4446 G) :
    ∀ x y z : G, x ◇ ((x ◇ y) ◇ x) = (z ◇ ((z ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ z)) ◇ (((z ◇ ((z ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ z)) ◇ z) ◇ (z ◇ ((z ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ z))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq9 : (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ≠ ((sK2 ◇ ((sK2 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ sK2)) ◇ (((sK2 ◇ ((sK2 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ sK2)) ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ sK2)))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose eq8 eq8
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq11
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ X2) ◇ X2) := superpose eq11 eq8
  have eq33 (X0 : G) : (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ≠ (X0 ◇ (((sK2 ◇ ((sK2 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ sK2)) ◇ sK2) ◇ X0)) := superpose eq11 eq9
  have eq39 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq11 eq10
  have eq44 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq10
  have eq50 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq11
  have eq51 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq8
  have eq55 (X0 X1 : G) : (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) ≠ (X1 ◇ (((sK2 ◇ ((sK2 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) ◇ sK2)) ◇ sK2) ◇ X1)) := superpose eq11 eq33
  have eq86 (X0 X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ (((X0 ◇ ((sK2 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X1))) ◇ X0)) ◇ sK2) ◇ X2)) := superpose eq11 eq55
  have eq142 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq8 eq20
  have eq144 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X3))) := superpose eq8 eq20
  have eq229 (X0 X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ ((((X0 ◇ (sK2 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X1)))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ sK2) ◇ X2)) := superpose eq8 eq86
  have eq973 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq44 eq11
  have eq974 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq44 eq20
  have eq1523 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq50 eq21
  have eq6962 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X1) = (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) := superpose eq20 eq973
  have eq6969 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq39 eq973
  have eq7530 (X0 X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ ((((X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) ◇ (((X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X1))) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X1)))) ◇ sK2) ◇ X2)) := superpose eq1523 eq229
  have eq8010 (X0 X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ ((((X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((((sK0 ◇ sK1) ◇ X1) ◇ ((sK0 ◇ sK1) ◇ X1)) ◇ ((sK0 ◇ sK1) ◇ X1)))) ◇ sK2) ◇ X2)) := superpose eq51 eq7530
  have eq8196 (X0 X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ ((((X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) ◇ sK2) ◇ X2)) := superpose eq6969 eq8010
  have eq8267 (X0 X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ ((((X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ sK2) ◇ X2)) := superpose eq51 eq8196
  have eq8284 (X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ (((((sK2 ◇ sK2) ◇ sK2) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ sK2) ◇ X2)) := superpose eq973 eq8267
  have eq17621 (X0 X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ (((((sK2 ◇ sK2) ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) ◇ sK2) ◇ X2)) := superpose eq50 eq8284
  have eq19106 (X0 X1 X2 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X2 ◇ (((X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) ◇ sK2) ◇ X2)) := superpose eq142 eq17621
  have eq20469 (X0 X1 X2 : G) : (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) ≠ ((X1 ◇ ((X2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X2)) ◇ X1)) ◇ ((sK2 ◇ sK2) ◇ sK2)) := superpose eq32 eq19106
  have eq29223 (X0 X1 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ ((X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) ◇ ((sK2 ◇ sK2) ◇ sK2)) := superpose eq144 eq20469
  have eq30940 (X0 X1 : G) : (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) ≠ (X0 ◇ (((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0)) := superpose eq974 eq29223
  have eq31054 (X1 : G) : (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) := superpose eq6962 eq30940
  have eq31112 (X1 : G) : (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) ≠ (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) := superpose eq51 eq31054
  have eq31857 : (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := superpose eq50 eq31112
  subsumption eq31857 rfl

theorem Equation3994_termDefinableFrom_Equation4446 :
    Law3994.TermDefinableFrom Law4446 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op (M.op x y) x)⟩, ?_, ?_⟩
  · rw [@Law3994.models_iff]
    exact @law3994_of_law4446 G M (Law4446.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩

/-- Equation 4458 `x ◇ (y ◇ x) = (z ◇ y) ◇ z` is term-definable from equation 4446 `x ◇ (y ◇ x) = (y ◇ y) ◇ y`,
via the term `x □ y := x ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ x)`. -/
private theorem law4458_of_law4446 [Magma G] (h : Equation4446 G) :
    ∀ x y z : G, x ◇ ((x ◇ (x ◇ ((y ◇ ((y ◇ (y ◇ (x ◇ y))) ◇ y)) ◇ x))) ◇ x) = (z ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ z)) ◇ (((z ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ z)) ◇ ((z ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ z)) ◇ (z ◇ (z ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ z))))) ◇ (z ◇ ((z ◇ (z ◇ (y ◇ z))) ◇ z))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq9 : (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) ◇ sK0))) ◇ sK0)) ≠ ((sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)) ◇ (((sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)) ◇ ((sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2))))) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq8
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose eq8 eq8
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq11
  have eq24 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq8 eq11
  have eq38 (X0 : G) : (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) ◇ sK0))) ◇ sK0)) ≠ (X0 ◇ (((sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)) ◇ ((sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2))))) ◇ X0)) := superpose eq11 eq9
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ X2) ◇ X2) := superpose eq11 eq8
  have eq48 (X0 : G) : (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) ◇ sK0))) ◇ sK0)) ≠ (X0 ◇ (((((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)) ◇ X0)) := superpose eq45 eq38
  have eq79 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq10
  have eq83 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq11
  have eq86 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq11
  have eq355 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X3))) := superpose eq8 eq22
  have eq357 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X5 ◇ ((X4 ◇ X1) ◇ X5))) := superpose eq22 eq22
  have eq480 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X2)) = ((X4 ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq22 eq11
  have eq547 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X3)) := superpose eq11 eq23
  have eq716 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq24
  have eq778 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq24 eq8
  have eq814 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq24 eq8
  have eq1573 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq79 eq22
  have eq1574 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq79 eq22
  have eq1575 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq79 eq23
  have eq1829 (X0 X1 : G) : (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) ◇ sK0))) ◇ sK0)) ≠ (((X0 ◇ X0) ◇ ((((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose eq83 eq48
  have eq2334 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq86 eq23
  have eq12469 (X0 : G) : (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) ◇ sK0))) ◇ sK0)) ≠ (X0 ◇ (((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ X0)) := superpose eq11 eq1829
  have eq12502 (X0 X1 : G) : (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ (X0 ◇ (sK0 ◇ X0))) ◇ sK1)) ◇ sK0))) ◇ sK0)) ≠ (X1 ◇ (((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ X1)) := superpose eq11 eq12469
  have eq12688 (X0 X1 X2 : G) : (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((X0 ◇ ((sK1 ◇ (X1 ◇ (sK0 ◇ X1))) ◇ X0)) ◇ sK0))) ◇ sK0)) ≠ (X2 ◇ (((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ X2)) := superpose eq11 eq12502
  have eq13425 (X0 X1 X2 X3 : G) : (X3 ◇ (((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ X3)) ≠ (X0 ◇ ((sK0 ◇ (sK0 ◇ ((X1 ◇ ((sK1 ◇ (X2 ◇ (sK0 ◇ X2))) ◇ X1)) ◇ sK0))) ◇ X0)) := superpose eq11 eq12688
  have eq16867 (X0 X1 X2 X3 : G) : (X2 ◇ (((sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ X2)) ≠ (X3 ◇ ((sK0 ◇ (X0 ◇ ((sK1 ◇ (X1 ◇ (sK0 ◇ X1))) ◇ X0))) ◇ X3)) := superpose eq2334 eq13425
  have eq18542 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((sK2 ◇ (X0 ◇ (sK1 ◇ X0))) ◇ sK2) ◇ X1)) ≠ (X2 ◇ ((sK0 ◇ (X3 ◇ ((sK1 ◇ (X4 ◇ (sK0 ◇ X4))) ◇ X3))) ◇ X2)) := superpose eq11 eq16867
  have eq38721 (X0 X1 X2 X3 : G) : (X0 ◇ (((sK2 ◇ (X1 ◇ (sK1 ◇ X1))) ◇ sK2) ◇ X0)) ≠ (X2 ◇ ((sK0 ◇ ((X3 ◇ (sK1 ◇ X3)) ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ X2)) := superpose eq1574 eq18542
  have eq38922 (X0 X1 X2 X3 : G) : (X1 ◇ (((sK2 ◇ (X2 ◇ (sK1 ◇ X2))) ◇ sK2) ◇ X1)) ≠ (X3 ◇ ((sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) ◇ X3)) := superpose eq23 eq38721
  have eq39446 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((sK2 ◇ (X4 ◇ (sK1 ◇ X4))) ◇ sK2) ◇ X3)) ≠ ((X0 ◇ (sK0 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ ((sK1 ◇ sK0) ◇ X2)) ◇ X1))) := superpose eq480 eq38922
  have eq58545 (X0 X1 X2 X3 : G) : (X1 ◇ (((sK2 ◇ (X2 ◇ (sK1 ◇ X2))) ◇ sK2) ◇ X1)) ≠ ((X3 ◇ (sK0 ◇ X3)) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := superpose eq355 eq39446
  have eq60806 (X0 X1 X2 X3 : G) : (X2 ◇ (((sK2 ◇ (X3 ◇ (sK1 ◇ X3))) ◇ sK2) ◇ X2)) ≠ (X0 ◇ ((X1 ◇ (sK1 ◇ X1)) ◇ X0)) := superpose eq357 eq58545
  have eq62170 (X0 X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X0 ◇ (((sK2 ◇ (X1 ◇ (sK1 ◇ X1))) ◇ sK2) ◇ X0)) := superpose eq814 eq60806
  have eq63803 (X0 X1 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ ((X0 ◇ ((sK2 ◇ (X1 ◇ (sK1 ◇ X1))) ◇ X0)) ◇ ((sK2 ◇ sK2) ◇ sK2)) := superpose eq547 eq62170
  have eq66023 : ((sK1 ◇ sK1) ◇ sK1) ≠ ((((sK2 ◇ sK2) ◇ sK2) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ sK2)) := superpose eq1575 eq63803
  have eq71003 (X0 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ ((X0 ◇ ((sK2 ◇ sK1) ◇ X0)) ◇ ((sK2 ◇ sK2) ◇ sK2)) := superpose eq86 eq66023
  have eq71182 (X0 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X0 ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0)) := superpose eq1573 eq71003
  have eq71184 (X0 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (X0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ X0)) := superpose eq45 eq71182
  have eq71635 (X0 : G) : ((sK1 ◇ sK1) ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ X0)))) := superpose eq716 eq71184
  have eq71841 : ((sK1 ◇ sK1) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK1) := superpose eq778 eq71635
  subsumption eq71841 rfl

theorem Equation4458_termDefinableFrom_Equation4446 :
    Law4458.TermDefinableFrom Law4446 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op (M.op x (M.op x (M.op y x))) x)⟩, ?_, ?_⟩
  · rw [@Law4458.models_iff]
    exact @law4458_of_law4446 G M (Law4446.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 1) (Term.var 0)))) (Term.var 0))), rfl⟩

/-- Equation 365 `x ◇ x = (y ◇ x) ◇ y` is term-definable from equation 281 `x = ((y ◇ y) ◇ x) ◇ y`,
via the term `x □ y := (x ◇ x) ◇ (y ◇ y)`. -/
private theorem law365_of_law281 [Magma G] (h : Equation281 G) :
    ∀ x y : G, (x ◇ x) ◇ (x ◇ x) = (((y ◇ y) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (x ◇ x))) ◇ (y ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ≠ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq8
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq13 eq13
  have eq24 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq21
  have eq30 : ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq24 eq9
  subsumption eq30 rfl

theorem Equation365_termDefinableFrom_Equation281 :
    Law365.TermDefinableFrom Law281 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op y y)⟩, ?_, ?_⟩
  · rw [@Law365.models_iff]
    exact @law365_of_law281 G M (Law281.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), rfl⟩

/-- Equation 4091 `x ◇ x = ((y ◇ y) ◇ x) ◇ y` is term-definable from equation 3685 `x ◇ x = (y ◇ y) ◇ (x ◇ y)`,
via the term `x □ y := (x ◇ x) ◇ (y ◇ y)`. -/
private theorem law4091_of_law3685 [Magma G] (h : Equation3685 G) :
    ∀ x y : G, (x ◇ x) ◇ (x ◇ x) = (((((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) ◇ (x ◇ x))) ◇ (y ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ≠ ((((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq8 eq8
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq8 eq8
  have eq100 (X0 X1 : G) : (X1 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq16 eq16
  have eq228 (X0 : G) : ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ≠ (((((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK0 ◇ sK0)) ◇ (((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)) ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := superpose eq10 eq9
  have eq248 : ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ≠ (((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := superpose eq8 eq228
  have eq269 : ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ≠ ((((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1)) := superpose eq8 eq248
  have eq276 : ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq100 eq269
  subsumption eq276 rfl

theorem Equation4091_termDefinableFrom_Equation3685 :
    Law4091.TermDefinableFrom Law3685 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op y y)⟩, ?_, ?_⟩
  · rw [@Law4091.models_iff]
    exact @law4091_of_law3685 G M (Law3685.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), rfl⟩

/-- Equation 365 `x ◇ x = (y ◇ x) ◇ y` is term-definable from equation 3959 `x ◇ y = (y ◇ (x ◇ z)) ◇ z`,
via the term `x □ y := x ◇ (x ◇ (y ◇ y))`. -/
private theorem law365_of_law3959 [Magma G] (h : Equation3959 G) :
    ∀ x y : G, x ◇ (x ◇ (x ◇ x)) = (y ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ (y ◇ y)) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq8 eq8
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq8
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X4)))) ◇ X1) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) := superpose eq10 eq10
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq10 eq8
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq10 eq8
  have eq38 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X4) ◇ (X1 ◇ (X0 ◇ (X3 ◇ X2)))) = (X3 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq11 eq11
  have eq46 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X3 ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq11
  have eq65 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X2))) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq11 eq28
  have eq74 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = ((((X2 ◇ X4) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) := superpose eq28 eq11
  have eq81 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = ((X4 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X4) := superpose eq17 eq74
  have eq85 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq28 eq81
  have eq107 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X1 ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq31 eq8
  have eq112 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq8 eq107
  have eq141 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X3) ◇ (X1 ◇ X2)) := superpose eq112 eq11
  have eq144 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq112 eq8
  have eq189 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X5 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X4)) = (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ X4)) := superpose eq10 eq46
  have eq200 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X4 ◇ X2) ◇ X3)) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq28 eq46
  have eq225 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X1)) := superpose eq31 eq46
  have eq238 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ X2) = (X3 ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq46 eq11
  have eq298 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = (X3 ◇ (X1 ◇ (X2 ◇ X4))) := superpose eq65 eq238
  have eq308 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq144 eq225
  have eq328 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ ((X4 ◇ X2) ◇ X3)) := superpose eq8 eq200
  have eq337 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X5 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X4)) = ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X4) ◇ X3))) := superpose eq65 eq189
  have eq370 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X1 ◇ X0))) = ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X4) ◇ X3))) := superpose eq328 eq337
  have eq787 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := superpose eq308 eq9
  have eq808 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0))))) := superpose eq38 eq787
  have eq872 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ sK1))) := superpose eq298 eq808
  have eq900 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := superpose eq85 eq872
  have eq914 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq11 eq900
  have eq922 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := superpose eq141 eq914
  have eq930 : (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq370 eq922
  have eq936 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq112 eq930
  have eq942 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq112 eq936
  subsumption eq942 rfl

theorem Equation365_termDefinableFrom_Equation3959 :
    Law365.TermDefinableFrom Law3959 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op x (M.op y y))⟩, ?_, ?_⟩
  · rw [@Law365.models_iff]
    exact @law365_of_law3959 G M (Law3959.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 1) (Term.var 1)))), rfl⟩

/-- Equation 4636 `(x ◇ y) ◇ x = (y ◇ x) ◇ y` is term-definable from equation 4679 `(x ◇ y) ◇ z = (y ◇ z) ◇ x`,
via the term `x □ y := x ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y)))`. -/
private theorem law4636_of_law4679 [Magma G] (h : Equation4679 G) :
    ∀ x y : G, (x ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇ ((x ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇ (x ◇ ((x ◇ x) ◇ x))) = (y ◇ (y ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ ((y ◇ (y ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ ((y ◇ y) ◇ y))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq8 eq8
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((X1 ◇ X3) ◇ (X2 ◇ X0)) := superpose eq8 eq8
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((X3 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq8 eq8
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq8 eq8
  have eq20 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) := superpose eq8 eq10
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = ((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X1) := superpose eq8 eq10
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) := superpose eq10 eq10
  have eq32 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ X3) = (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X4)) := superpose eq8 eq10
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X5)) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X5) ◇ X4) := superpose eq10 eq10
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X3 ◇ (X1 ◇ X2))) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) := superpose eq10 eq10
  have eq38 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ (X3 ◇ X1)) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) := superpose eq10 eq10
  have eq41 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) := superpose eq10 eq10
  have eq45 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq10 eq8
  have eq48 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = ((X1 ◇ X4) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq10 eq8
  have eq49 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq10 eq8
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq10 eq8
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X4) ◇ ((X0 ◇ X2) ◇ X3)) = ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq49 eq48
  have eq55 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ X4))) := superpose eq49 eq41
  have eq56 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ (X3 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq49 eq38
  have eq57 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X5)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X5)) ◇ X4) := superpose eq49 eq34
  have eq63 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X5))) := superpose eq49 eq23
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X4) ◇ ((X0 ◇ X2) ◇ X3)) = ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) := superpose eq49 eq51
  have eq67 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ (X3 ◇ X1)) = ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) := superpose eq49 eq56
  have eq68 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X5)) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X5 ◇ X4)) := superpose eq49 eq57
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X1) = ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ X5)))) := superpose eq49 eq63
  have eq75 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X5)) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X5 ◇ X4))) := superpose eq49 eq68
  have eq78 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ X5)))) = ((X4 ◇ (X0 ◇ X2)) ◇ (X5 ◇ (X3 ◇ X1))) := superpose eq55 eq72
  have eq80 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X5 ◇ X4))) = (((X0 ◇ X2) ◇ X3) ◇ (X5 ◇ (X1 ◇ X4))) := superpose eq67 eq75
  have eq82 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ X5)))) = ((X0 ◇ X4) ◇ (X2 ◇ (X5 ◇ (X3 ◇ X1)))) := superpose eq49 eq78
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X5 ◇ X4))) = ((X0 ◇ X2) ◇ ((X1 ◇ X4) ◇ (X5 ◇ X3))) := superpose eq67 eq80
  have eq134 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X2 ◇ X0) ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) := superpose eq11 eq11
  have eq136 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = ((X2 ◇ X4) ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq11 eq11
  have eq137 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = ((X3 ◇ X4) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq10 eq11
  have eq148 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = (((X4 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X5) ◇ X1) := superpose eq10 eq11
  have eq154 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = (((X1 ◇ X4) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X5) := superpose eq10 eq11
  have eq165 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = (((X3 ◇ X0) ◇ X4) ◇ (X2 ◇ X1)) := superpose eq11 eq10
  have eq166 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X1 ◇ (X3 ◇ X0)) ◇ X2) := superpose eq11 eq8
  have eq188 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = ((X3 ◇ X0) ◇ (X1 ◇ (X2 ◇ X4))) := superpose eq67 eq165
  have eq196 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = (((X0 ◇ X2) ◇ (X1 ◇ X4)) ◇ (X3 ◇ X5)) := superpose eq49 eq154
  have eq202 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = ((((X0 ◇ X2) ◇ X4) ◇ (X3 ◇ X5)) ◇ X1) := superpose eq49 eq148
  have eq210 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) = ((X3 ◇ X4) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq49 eq137
  have eq211 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) = ((X2 ◇ X4) ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq49 eq136
  have eq221 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) = ((X3 ◇ X0) ◇ (X1 ◇ (X2 ◇ X4))) := superpose eq49 eq188
  have eq229 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((X1 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X3 ◇ X5))) := superpose eq49 eq196
  have eq235 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ (X5 ◇ X1)) := superpose eq49 eq202
  have eq242 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) = ((X3 ◇ X4) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq49 eq210
  have eq243 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) = ((X2 ◇ X4) ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq49 eq211
  have eq252 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) = ((X3 ◇ X0) ◇ (X1 ◇ (X2 ◇ X4))) := superpose eq49 eq221
  have eq259 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((X0 ◇ X1) ◇ (X2 ◇ (X4 ◇ (X3 ◇ X5)))) := superpose eq49 eq229
  have eq263 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = (((X0 ◇ X2) ◇ X3) ◇ (X4 ◇ (X5 ◇ X1))) := superpose eq49 eq235
  have eq281 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = ((X0 ◇ X2) ◇ ((X5 ◇ X1) ◇ (X4 ◇ X3))) := superpose eq67 eq263
  have eq287 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X5 ◇ X4))) = ((X0 ◇ X2) ◇ ((X5 ◇ X1) ◇ (X4 ◇ X3))) := superpose eq49 eq281
  have eq290 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X5 ◇ X4)))) = ((X0 ◇ X2) ◇ ((X5 ◇ X1) ◇ (X4 ◇ X3))) := superpose eq49 eq287
  have eq349 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X5) = ((X5 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X4) := superpose eq10 eq13
  have eq390 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X5) = ((X0 ◇ X5) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq13 eq11
  have eq403 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X2 ◇ X5))) = ((X0 ◇ X5) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq55 eq390
  have eq433 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X5) = ((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ (X3 ◇ X4)) := superpose eq49 eq349
  have eq457 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ (X2 ◇ X5)))) = ((X0 ◇ X5) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq49 eq403
  have eq482 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X5) = (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (X3 ◇ X5))) := superpose eq67 eq433
  have eq520 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X5) = ((X0 ◇ X1) ◇ ((X3 ◇ X5) ◇ (X4 ◇ X2))) := superpose eq67 eq482
  have eq547 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X5) = ((X0 ◇ X1) ◇ (X5 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq290 eq520
  have eq564 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X4 ◇ (X0 ◇ X3))) ◇ (X2 ◇ X5)) = ((X0 ◇ X1) ◇ (X5 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq49 eq547
  have eq577 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X5))) = ((X0 ◇ X1) ◇ (X5 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq49 eq564
  have eq619 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X4) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X5) = ((X5 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) := superpose eq10 eq14
  have eq646 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X5 ◇ X4)) = (((X4 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X5) ◇ X0) := superpose eq14 eq11
  have eq659 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = ((((X3 ◇ X4) ◇ X0) ◇ X1) ◇ X2) := superpose eq14 eq10
  have eq698 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq55 eq659
  have eq708 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X5 ◇ X4)) = ((((X2 ◇ X3) ◇ X4) ◇ (X1 ◇ X5)) ◇ X0) := superpose eq49 eq646
  have eq729 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X4) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X5) = (((X0 ◇ X1) ◇ X5) ◇ ((X2 ◇ X3) ◇ X4)) := superpose eq49 eq619
  have eq775 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq49 eq698
  have eq781 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X5 ◇ X4)) = ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X5 ◇ X0)) := superpose eq49 eq708
  have eq797 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X4) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X5) = ((X0 ◇ X1) ◇ (X4 ◇ ((X2 ◇ X3) ◇ X5))) := superpose eq67 eq729
  have eq828 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq49 eq775
  have eq832 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X5 ◇ X4)) = (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ (X5 ◇ X0))) := superpose eq49 eq781
  have eq846 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X2) ◇ (X1 ◇ X4)) ◇ (X3 ◇ X5)) = ((X0 ◇ X1) ◇ (X4 ◇ ((X2 ◇ X3) ◇ X5))) := superpose eq49 eq797
  have eq871 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X5 ◇ X4)) = ((X2 ◇ X3) ◇ ((X5 ◇ X0) ◇ (X4 ◇ X1))) := superpose eq67 eq832
  have eq877 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X3 ◇ X5))) = ((X0 ◇ X1) ◇ (X4 ◇ ((X2 ◇ X3) ◇ X5))) := superpose eq49 eq846
  have eq891 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X5 ◇ X4)) = ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X5 ◇ X4)))) := superpose eq290 eq871
  have eq894 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X4 ◇ (X3 ◇ X5)))) = ((X0 ◇ X1) ◇ (X4 ◇ ((X2 ◇ X3) ◇ X5))) := superpose eq49 eq877
  have eq905 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ (X5 ◇ X3))) = ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X5 ◇ X4)))) := superpose eq67 eq891
  have eq912 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X4 ◇ (X5 ◇ X3)))) = ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X5 ◇ X4)))) := superpose eq49 eq905
  have eq1395 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = (((X4 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X5) ◇ X3) := superpose eq49 eq11
  have eq1450 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = (((X1 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) ◇ X3) := superpose eq49 eq1395
  have eq1510 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = (((X0 ◇ X2) ◇ (X1 ◇ X4)) ◇ (X5 ◇ X3)) := superpose eq49 eq1450
  have eq1558 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X5 ◇ X3))) := superpose eq49 eq1510
  have eq1595 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4)) = ((X0 ◇ X1) ◇ (X2 ◇ (X4 ◇ (X5 ◇ X3)))) := superpose eq49 eq1558
  have eq1624 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X5 ◇ X4))) = ((X0 ◇ X1) ◇ (X2 ◇ (X4 ◇ (X5 ◇ X3)))) := superpose eq49 eq1595
  have eq1641 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X5 ◇ X4)))) = ((X0 ◇ X1) ◇ (X2 ◇ (X4 ◇ (X5 ◇ X3)))) := superpose eq49 eq1624
  have eq2277 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = ((X0 ◇ (X2 ◇ X1)) ◇ (X4 ◇ X3)) := superpose eq50 eq166
  have eq2415 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = ((X2 ◇ X0) ◇ (X1 ◇ (X4 ◇ X3))) := superpose eq49 eq2277
  have eq2480 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) = ((X2 ◇ X0) ◇ (X1 ◇ (X4 ◇ X3))) := superpose eq49 eq2415
  have eq2534 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) = ((X2 ◇ X0) ◇ (X1 ◇ (X4 ◇ X3))) := superpose eq49 eq2480
  have eq2746 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X6) = (((X6 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ (X0 ◇ X5)) := superpose eq20 eq20
  have eq2799 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ (X6 ◇ X7)) := superpose eq20 eq20
  have eq2813 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X5)) = ((((X1 ◇ X0) ◇ X4) ◇ X5) ◇ (X2 ◇ X3)) := superpose eq14 eq20
  have eq2870 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X6) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4))) = ((X0 ◇ X6) ◇ (X5 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) := superpose eq20 eq50
  have eq3010 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X6) ◇ (X5 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) = ((X5 ◇ X6) ◇ (X2 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq290 eq2870
  have eq3060 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X5)) = (((X1 ◇ X0) ◇ X4) ◇ (X3 ◇ (X2 ◇ X5))) := superpose eq67 eq2813
  have eq3071 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ (X7 ◇ (X6 ◇ X5))) := superpose eq67 eq2799
  have eq3116 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X6) = ((X6 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X5 ◇ (X0 ◇ X4))) := superpose eq67 eq2746
  have eq3255 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X5)) = ((X1 ◇ X0) ◇ ((X2 ◇ X5) ◇ (X3 ◇ X4))) := superpose eq67 eq3060
  have eq3266 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X4 ◇ (X7 ◇ (X6 ◇ X5)))) := superpose eq49 eq3071
  have eq3308 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X6) = (((X1 ◇ X2) ◇ X6) ◇ (X3 ◇ (X5 ◇ (X0 ◇ X4)))) := superpose eq49 eq3116
  have eq3433 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X5)) = ((X1 ◇ X0) ◇ (X5 ◇ (X4 ◇ (X2 ◇ X3)))) := superpose eq290 eq3255
  have eq3444 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = (((X0 ◇ X1) ◇ X3) ◇ (X2 ◇ (X4 ◇ (X7 ◇ (X6 ◇ X5))))) := superpose eq49 eq3266
  have eq3479 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X6) = ((X1 ◇ X2) ◇ ((X5 ◇ (X0 ◇ X4)) ◇ (X3 ◇ X6))) := superpose eq67 eq3308
  have eq3589 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X4 ◇ X3))) = ((X1 ◇ X0) ◇ (X5 ◇ (X4 ◇ (X2 ◇ X3)))) := superpose eq67 eq3433
  have eq3596 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((X0 ◇ X1) ◇ ((X4 ◇ (X7 ◇ (X6 ◇ X5))) ◇ (X2 ◇ X3))) := superpose eq67 eq3444
  have eq3621 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X6) = ((X1 ◇ X2) ◇ ((X0 ◇ X4) ◇ (X6 ◇ (X5 ◇ X3)))) := superpose eq290 eq3479
  have eq3714 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X5 ◇ (X4 ◇ X3)))) = ((X1 ◇ X0) ◇ (X5 ◇ (X4 ◇ (X2 ◇ X3)))) := superpose eq49 eq3589
  have eq3717 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((X0 ◇ X1) ◇ ((X7 ◇ (X6 ◇ X5)) ◇ (X3 ◇ (X4 ◇ X2)))) := superpose eq290 eq3596
  have eq3737 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X6) = ((X1 ◇ X2) ◇ (X4 ◇ ((X5 ◇ X3) ◇ (X0 ◇ X6)))) := superpose eq290 eq3621
  have eq3807 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((X0 ◇ X1) ◇ ((X6 ◇ X5) ◇ ((X4 ◇ X2) ◇ (X7 ◇ X3)))) := superpose eq290 eq3717
  have eq3824 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ X4) ◇ (X0 ◇ X1)) ◇ (X5 ◇ (X2 ◇ X6))) = ((X1 ◇ X2) ◇ (X4 ◇ ((X5 ◇ X3) ◇ (X0 ◇ X6)))) := superpose eq55 eq3737
  have eq3886 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((X0 ◇ X1) ◇ (X5 ◇ ((X7 ◇ X3) ◇ (X6 ◇ (X4 ◇ X2))))) := superpose eq290 eq3807
  have eq3901 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ (X1 ◇ (X5 ◇ (X2 ◇ X6)))) = ((X1 ◇ X2) ◇ (X4 ◇ ((X5 ◇ X3) ◇ (X0 ◇ X6)))) := superpose eq49 eq3824
  have eq3951 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ (X5 ◇ ((X7 ◇ X3) ◇ (X6 ◇ (X4 ◇ X2))))) = (((X0 ◇ X5) ◇ X6) ◇ (X4 ◇ (((X1 ◇ X2) ◇ X3) ◇ X7))) := superpose eq67 eq3886
  have eq3962 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X0) ◇ (X4 ◇ (X1 ◇ (X5 ◇ (X2 ◇ X6))))) = ((X1 ◇ X2) ◇ (X4 ◇ ((X5 ◇ X3) ◇ (X0 ◇ X6)))) := superpose eq49 eq3901
  have eq3998 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ (X5 ◇ ((X7 ◇ X3) ◇ (X6 ◇ (X4 ◇ X2))))) = ((X0 ◇ X5) ◇ ((((X1 ◇ X2) ◇ X3) ◇ X7) ◇ (X4 ◇ X6))) := superpose eq67 eq3951
  have eq4031 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ (X5 ◇ ((X7 ◇ X3) ◇ (X6 ◇ (X4 ◇ X2))))) = ((X0 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)))) := superpose eq290 eq3998
  have eq4300 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ (X6 ◇ X7)) = ((((X1 ◇ X5) ◇ X6) ◇ X7) ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) := superpose eq21 eq20
  have eq4377 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ (X6 ◇ X7)) = (((X1 ◇ X5) ◇ X6) ◇ (X4 ◇ (((X2 ◇ X0) ◇ X3) ◇ X7))) := superpose eq67 eq4300
  have eq4612 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ (X6 ◇ X7)) = ((X1 ◇ X5) ◇ ((((X2 ◇ X0) ◇ X3) ◇ X7) ◇ (X4 ◇ X6))) := superpose eq67 eq4377
  have eq4827 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ (X6 ◇ X7)) = ((X1 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)))) := superpose eq290 eq4612
  have eq5025 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ (X7 ◇ (X6 ◇ X5))) = ((X1 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)))) := superpose eq67 eq4827
  have eq5176 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X4 ◇ (X7 ◇ (X6 ◇ X5)))) = ((X1 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)))) := superpose eq49 eq5025
  have eq5298 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X2 ◇ (X4 ◇ (X7 ◇ (X6 ◇ X5))))) = ((X1 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)))) := superpose eq49 eq5176
  have eq5390 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ ((X4 ◇ (X7 ◇ (X6 ◇ X5))) ◇ (X2 ◇ X3))) = ((X1 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)))) := superpose eq67 eq5298
  have eq5471 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ ((X7 ◇ (X6 ◇ X5)) ◇ (X3 ◇ (X4 ◇ X2)))) = ((X1 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)))) := superpose eq290 eq5390
  have eq5530 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ ((X6 ◇ X5) ◇ ((X4 ◇ X2) ◇ (X7 ◇ X3)))) = ((X1 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)))) := superpose eq290 eq5471
  have eq5571 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ (X5 ◇ ((X7 ◇ X3) ◇ (X6 ◇ (X4 ◇ X2))))) = ((X1 ◇ X5) ◇ (X7 ◇ (X6 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)))) := superpose eq290 eq5530
  have eq5665 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X6) = (((X4 ◇ (X2 ◇ X1)) ◇ X6) ◇ ((X3 ◇ X0) ◇ X5)) := superpose eq50 eq32
  have eq5756 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ (X4 ◇ X5)) = ((((X3 ◇ X4) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X5) ◇ X6) := superpose eq49 eq32
  have eq5796 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ X4) ◇ X6) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((((X4 ◇ (X2 ◇ X1)) ◇ X5) ◇ (X3 ◇ X0)) ◇ X6) := superpose eq50 eq32
  have eq6117 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ X4) ◇ X6) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((X3 ◇ ((X4 ◇ (X2 ◇ X1)) ◇ X5)) ◇ (X0 ◇ X6)) := superpose eq49 eq5796
  have eq6157 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ (X4 ◇ X5)) = (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X5 ◇ (X4 ◇ X6))) := superpose eq55 eq5756
  have eq6238 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X6) = ((X4 ◇ (X2 ◇ X1)) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X6))) := superpose eq67 eq5665
  have eq6380 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ X4) ◇ X6) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = (((X4 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X5 ◇ (X0 ◇ X6))) := superpose eq49 eq6117
  have eq6418 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ (X4 ◇ X5)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X4 ◇ X6) ◇ (X5 ◇ X3))) := superpose eq67 eq6157
  have eq6496 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X6) = ((X2 ◇ X4) ◇ (X1 ◇ (X5 ◇ ((X3 ◇ X0) ◇ X6)))) := superpose eq49 eq6238
  have eq6623 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ X4) ◇ X6) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((X4 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X6) ◇ (X5 ◇ X3))) := superpose eq67 eq6380
  have eq6659 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ (X4 ◇ X5)) = ((X1 ◇ (X0 ◇ X2)) ◇ (X6 ◇ (X3 ◇ (X4 ◇ X5)))) := superpose eq290 eq6418
  have eq6727 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ (X5 ◇ ((X2 ◇ X3) ◇ X6))) = ((X2 ◇ X4) ◇ (X1 ◇ (X5 ◇ ((X3 ◇ X0) ◇ X6)))) := superpose eq55 eq6496
  have eq6826 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ X4) ◇ X6) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((X4 ◇ (X2 ◇ X1)) ◇ (X6 ◇ (X3 ◇ (X0 ◇ X5)))) := superpose eq290 eq6623
  have eq6860 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ (X4 ◇ X5)) = ((X0 ◇ X1) ◇ (X2 ◇ (X6 ◇ (X3 ◇ (X4 ◇ X5))))) := superpose eq49 eq6659
  have eq6920 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X4) ◇ (X1 ◇ (X5 ◇ ((X2 ◇ X3) ◇ X6)))) = ((X2 ◇ X4) ◇ (X1 ◇ (X5 ◇ ((X3 ◇ X0) ◇ X6)))) := superpose eq49 eq6727
  have eq7005 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ X4) ◇ X6) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((X2 ◇ X4) ◇ (X1 ◇ (X6 ◇ (X3 ◇ (X0 ◇ X5))))) := superpose eq49 eq6826
  have eq7030 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X5 ◇ (X4 ◇ X6))) = ((X0 ◇ X1) ◇ (X2 ◇ (X6 ◇ (X3 ◇ (X4 ◇ X5))))) := superpose eq67 eq6860
  have eq7138 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ X4) ◇ X6) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2)))) = ((X2 ◇ X4) ◇ (X1 ◇ (X6 ◇ (X3 ◇ (X0 ◇ X5))))) := superpose eq290 eq7005
  have eq7160 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X5 ◇ (X4 ◇ X6)))) = ((X0 ◇ X1) ◇ (X2 ◇ (X6 ◇ (X3 ◇ (X4 ◇ X5))))) := superpose eq49 eq7030
  have eq7241 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X4) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X6))) = ((X2 ◇ X4) ◇ (X1 ◇ (X6 ◇ (X3 ◇ (X0 ◇ X5))))) := superpose eq67 eq7138
  have eq7263 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X5 ◇ (X4 ◇ X6))))) = ((X0 ◇ X1) ◇ (X2 ◇ (X6 ◇ (X3 ◇ (X4 ◇ X5))))) := superpose eq49 eq7160
  have eq7327 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X6 ◇ (X3 ◇ X1)))) = ((X2 ◇ X4) ◇ (X1 ◇ (X6 ◇ (X3 ◇ (X0 ◇ X5))))) := superpose eq290 eq7241
  have eq7398 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X4) ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X6)))) = ((X2 ◇ X4) ◇ (X1 ◇ (X6 ◇ (X3 ◇ (X0 ◇ X5))))) := superpose eq290 eq7327
  have eq7591 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = (((((X2 ◇ X1) ◇ X5) ◇ X6) ◇ X4) ◇ (X3 ◇ X0)) := superpose eq50 eq37
  have eq7604 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((((((X0 ◇ X2) ◇ X3) ◇ X5) ◇ X6) ◇ X4) ◇ X1) := superpose eq10 eq37
  have eq7643 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X5 ◇ X2) ◇ X3) ◇ (X1 ◇ (X4 ◇ X0))) ◇ X6) = ((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4))) := superpose eq166 eq37
  have eq7691 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ X5) ◇ X4) = (((X1 ◇ (X0 ◇ X2)) ◇ X4) ◇ (X5 ◇ (X3 ◇ X6))) := superpose eq49 eq37
  have eq8123 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ X5) ◇ X4) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X6) ◇ (X5 ◇ X4))) := superpose eq67 eq7691
  have eq8169 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X5 ◇ X2) ◇ X3) ◇ (X1 ◇ (X4 ◇ X0))) ◇ X6) = ((X5 ◇ X6) ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq290 eq7643
  have eq8208 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((X6 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ (X5 ◇ X1))) := superpose eq55 eq7604
  have eq8221 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((((X2 ◇ X1) ◇ X5) ◇ X6) ◇ (X0 ◇ (X3 ◇ X4))) := superpose eq67 eq7591
  have eq8408 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ X5) ◇ X4) = ((X1 ◇ (X0 ◇ X2)) ◇ (X6 ◇ (X4 ◇ (X3 ◇ X5)))) := superpose eq290 eq8123
  have eq8453 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X6) ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X1 ◇ ((X5 ◇ X2) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X6)) := superpose eq49 eq8169
  have eq8486 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = (((X0 ◇ X2) ◇ X6) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X1)))) := superpose eq49 eq8208
  have eq8499 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = (((X2 ◇ X1) ◇ X5) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X6))) := superpose eq67 eq8221
  have eq8657 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X6) ◇ X5) ◇ X4) = ((X0 ◇ X1) ◇ (X2 ◇ (X6 ◇ (X4 ◇ (X3 ◇ X5))))) := superpose eq49 eq8408
  have eq8699 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X6) ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X3))))) = (((X5 ◇ X2) ◇ X1) ◇ (X3 ◇ ((X4 ◇ X0) ◇ X6))) := superpose eq49 eq8453
  have eq8725 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((X0 ◇ X2) ◇ ((X4 ◇ (X5 ◇ X1)) ◇ (X3 ◇ X6))) := superpose eq67 eq8486
  have eq8738 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = (((X2 ◇ X1) ◇ X5) ◇ (X4 ◇ (X6 ◇ (X3 ◇ X0)))) := superpose eq290 eq8499
  have eq8871 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X6 ◇ (X0 ◇ X1)) ◇ (X5 ◇ ((X2 ◇ X3) ◇ X4))) = ((X0 ◇ X1) ◇ (X2 ◇ (X6 ◇ (X4 ◇ (X3 ◇ X5))))) := superpose eq55 eq8657
  have eq8906 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X6) ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X5 ◇ X2) ◇ (((X4 ◇ X0) ◇ X6) ◇ (X3 ◇ X1))) := superpose eq67 eq8699
  have eq8920 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((X0 ◇ X2) ◇ ((X5 ◇ X1) ◇ (X6 ◇ (X4 ◇ X3)))) := superpose eq290 eq8725
  have eq8933 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((X2 ◇ X1) ◇ ((X6 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X5))) := superpose eq67 eq8738
  have eq9037 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X6) ◇ (X1 ◇ (X5 ◇ ((X2 ◇ X3) ◇ X4)))) = ((X0 ◇ X1) ◇ (X2 ◇ (X6 ◇ (X4 ◇ (X3 ◇ X5))))) := superpose eq49 eq8871
  have eq9061 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X6) ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X5 ◇ X2) ◇ (X6 ◇ (X1 ◇ ((X4 ◇ X0) ◇ X3)))) := superpose eq290 eq8906
  have eq9063 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((X0 ◇ X2) ◇ (X1 ◇ ((X4 ◇ X3) ◇ (X5 ◇ X6)))) := superpose eq290 eq8920
  have eq9075 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ (X5 ◇ (X6 ◇ X4)))) := superpose eq290 eq8933
  have eq9163 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6)))) = ((X0 ◇ X2) ◇ (X1 ◇ ((X4 ◇ X3) ◇ (X5 ◇ X6)))) := superpose eq49 eq9063
  have eq9173 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = ((X2 ◇ X1) ◇ (X0 ◇ ((X6 ◇ X4) ◇ (X3 ◇ X5)))) := superpose eq290 eq9075
  have eq9249 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6))))) = ((X0 ◇ X2) ◇ (X1 ◇ ((X4 ◇ X3) ◇ (X5 ◇ X6)))) := superpose eq49 eq9163
  have eq9259 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6)))) = ((X2 ◇ X1) ◇ (X0 ◇ ((X6 ◇ X4) ◇ (X3 ◇ X5)))) := superpose eq49 eq9173
  have eq9323 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6)))) = ((X2 ◇ X1) ◇ (X0 ◇ (X4 ◇ (X6 ◇ (X3 ◇ X5))))) := superpose eq9249 eq9259
  have eq9359 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6))))) = ((X2 ◇ X1) ◇ (X0 ◇ (X4 ◇ (X6 ◇ (X3 ◇ X5))))) := superpose eq49 eq9323
  have eq12106 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) = ((((X0 ◇ (X4 ◇ X1)) ◇ X2) ◇ X3) ◇ X5) := superpose eq64 eq45
  have eq12146 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) = ((X2 ◇ X0) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X5))) := superpose eq55 eq12106
  have eq12401 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X4 ◇ X5)) = ((X2 ◇ X0) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X5))) := superpose eq49 eq12146
  have eq12585 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X5))) = ((X2 ◇ X0) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X5))) := superpose eq49 eq12401
  have eq12639 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X5)))) = ((X2 ◇ X0) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X5))) := superpose eq49 eq12585
  have eq14591 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X5) = (((X1 ◇ X3) ◇ X5) ◇ ((X4 ◇ X2) ◇ X0)) := superpose eq32 eq134
  have eq14956 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X5) = ((X1 ◇ X3) ◇ (X0 ◇ ((X4 ◇ X2) ◇ X5))) := superpose eq67 eq14591
  have eq15108 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X5) = ((X1 ◇ X3) ◇ (X0 ◇ (X2 ◇ (X4 ◇ X5)))) := superpose eq12639 eq14956
  have eq15233 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X2 ◇ X5))) = ((X1 ◇ X3) ◇ (X0 ◇ (X2 ◇ (X4 ◇ X5)))) := superpose eq55 eq15108
  have eq15302 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ (X2 ◇ X5)))) = ((X1 ◇ X3) ◇ (X0 ◇ (X2 ◇ (X4 ◇ X5)))) := superpose eq49 eq15233
  have eq45596 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK1 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))))) := superpose eq84 eq9
  have eq46153 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)))))) := superpose eq82 eq45596
  have eq46225 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)))))) := superpose eq3714 eq46153
  have eq46254 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ sK1))) := superpose eq3010 eq46225
  have eq46269 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)))))) := superpose eq828 eq46254
  have eq46274 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ sK0)))))) := superpose eq5571 eq46269
  have eq46276 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ sK0)))))) := superpose eq3714 eq46274
  have eq46278 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)))))) := superpose eq242 eq46276
  have eq46280 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1))) ◇ sK1))) := superpose eq3010 eq46278
  have eq46282 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)))))) := superpose eq2534 eq46280
  have eq46284 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := superpose eq9037 eq46282
  have eq46286 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)))))) := superpose eq8 eq46284
  have eq46288 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))))) := superpose eq242 eq46286
  have eq46290 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))))) := superpose eq243 eq46288
  have eq46292 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))))))))) := superpose eq82 eq46290
  have eq46294 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))))))))) := superpose eq894 eq46292
  have eq46296 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1))))))) := superpose eq82 eq46294
  have eq46298 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))))))))) := superpose eq912 eq46296
  have eq46300 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)))))))) := superpose eq3962 eq46298
  have eq46302 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)))))))) := superpose eq6920 eq46300
  have eq46304 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))))))))) := superpose eq9061 eq46302
  have eq46306 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))))) := superpose eq9359 eq46304
  have eq46308 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)))))))) := superpose eq8 eq46306
  have eq46310 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK0)))))))) := superpose eq259 eq46308
  have eq46312 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1)))))))) := superpose eq2534 eq46310
  have eq46314 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))))))))) := superpose eq457 eq46312
  have eq46316 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))))))) := superpose eq894 eq46314
  have eq46318 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)))))))))) := superpose eq1641 eq46316
  have eq46320 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))) := superpose eq9037 eq46318
  have eq46322 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0))))))))) := superpose eq4031 eq46320
  have eq46324 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0))))))))) := superpose eq3714 eq46322
  have eq46326 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)))))))) := superpose eq7398 eq46324
  have eq46328 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))))))))) := superpose eq1641 eq46326
  have eq46330 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))))))))) := superpose eq7263 eq46328
  have eq46332 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)))))))))) := superpose eq64 eq46330
  have eq46334 : ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) := superpose eq50 eq46332
  have eq46336 : ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) := superpose eq242 eq46334
  have eq46338 : ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) := superpose eq252 eq46336
  have eq46340 : ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) := superpose eq82 eq46338
  have eq46342 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))))))) := superpose eq15302 eq46340
  have eq46344 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))))))) := superpose eq9061 eq46342
  have eq46346 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))))))) := superpose eq9359 eq46344
  have eq46348 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)))))))) := superpose eq252 eq46346
  have eq46350 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK0)))))))) := superpose eq577 eq46348
  have eq46352 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)))))))) := superpose eq2534 eq46350
  have eq46354 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))))))))) := superpose eq577 eq46352
  have eq46356 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)))))))) := superpose eq2534 eq46354
  have eq46358 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))))))))) := superpose eq457 eq46356
  have eq46360 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))))))))) := superpose eq252 eq46358
  have eq46362 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)))))))) := superpose eq894 eq46360
  have eq46364 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)))))))) := superpose eq82 eq46362
  have eq46366 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1))))))) := superpose eq894 eq46364
  have eq46368 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))))))))) := superpose eq2534 eq46366
  have eq46370 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)))))))))) := superpose eq64 eq46368
  have eq46372 : ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))))) := superpose eq50 eq46370
  subsumption eq46372 rfl

theorem Equation4636_termDefinableFrom_Equation4679 :
    Law4636.TermDefinableFrom Law4679 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op x (M.op y (M.op (M.op y y) y)))⟩, ?_, ?_⟩
  · rw [@Law4636.models_iff]
    exact @law4636_of_law4679 G M (Law4679.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 1) (tm (tm (Term.var 1) (Term.var 1)) (Term.var 1))))), rfl⟩

/-- Equation 4413 `x ◇ (x ◇ y) = (y ◇ z) ◇ z` is term-definable from equation 4216 `x ◇ y = ((z ◇ y) ◇ z) ◇ x`,
via the term `x □ y := (x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))`. -/
private theorem law4413_of_law4216 [Magma G] (h : Equation4216 G) :
    ∀ x y z : G, (x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇ ((x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇ (x ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))))) = (((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z) ◇ ((((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z) ◇ (((y ◇ z) ◇ ((y ◇ z) ◇ (y ◇ z))) ◇ z)) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ ((((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) ◇ sK2))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2) := superpose eq8 eq8
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq8 eq11
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ ((X1 ◇ X3) ◇ X3)) := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X2) := superpose eq8 eq11
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq11
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq15 eq13
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq15 eq12
  have eq20 (X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq8 eq18
  have eq21 (X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq8 eq19
  have eq30 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq10 eq10
  have eq49 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq15 eq30
  have eq60 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X3 ◇ ((X4 ◇ X1) ◇ X4)) ◇ X1) ◇ X2) := superpose eq21 eq49
  have eq69 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X1 ◇ (((X4 ◇ X1) ◇ X4) ◇ X3)) ◇ X2) := superpose eq15 eq60
  have eq75 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X3 ◇ X1)) ◇ X2) := superpose eq8 eq69
  have eq105 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq8
  have eq111 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ ((sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) ◇ ((sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))))) := superpose eq14 eq9
  have eq117 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq20 eq111
  have eq136 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ (((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1) := superpose eq75 eq117
  have eq142 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq15 eq136
  have eq147 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK1)) := superpose eq75 eq142
  have eq148 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2))) := superpose eq15 eq147
  have eq149 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := superpose eq15 eq148
  have eq150 : ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq20 eq149
  have eq151 : (sK1 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq20 eq150
  have eq152 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := superpose eq105 eq151
  have eq153 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq15 eq152
  have eq154 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := superpose eq105 eq153
  have eq155 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := superpose eq15 eq154
  have eq156 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq15 eq155
  have eq157 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq21 eq156
  subsumption eq157 rfl

theorem Equation4413_termDefinableFrom_Equation4216 :
    Law4413.TermDefinableFrom Law4216 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x y) (M.op (M.op x y) (M.op x y))⟩, ?_, ?_⟩
  · rw [@Law4413.models_iff]
    exact @law4413_of_law4216 G M (Law4216.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (Term.var 1)))), rfl⟩

/-- Equation 4157 `x ◇ y = ((y ◇ x) ◇ y) ◇ x` is term-definable from equation 2316 `x = (y ◇ (x ◇ (z ◇ y))) ◇ z`,
via the term `x □ y := (x ◇ x) ◇ (((x ◇ y) ◇ x) ◇ y)`. -/
private theorem law4157_of_law2316 [Magma G] (h : Equation2316 G) :
    ∀ x y : G, (x ◇ x) ◇ (((x ◇ y) ◇ x) ◇ y) = (((((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ (((((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x)) ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ (((((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x)) ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ y))) ◇ (((((((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ (((((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x)) ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ y)) ◇ x) ◇ ((((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ (((((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x)) ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ y))) ◇ x) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ sK1)) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ sK1))) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ sK1)) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ sK1))) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3)))) = X2 := superpose eq8 eq8
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2))) = ((X1 ◇ X0) ◇ X3) := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X2))) = ((X1 ◇ X0) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X4)))) := superpose eq8 eq10
  have eq14 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X4)))) = X2 := superpose eq8 eq10
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X4)))) = X3 := superpose eq10 eq10
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) := superpose eq10 eq8
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X2) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1)) = X3 := superpose eq11 eq15
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) ◇ X1)) = X2 := superpose eq11 eq14
  have eq26 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X2 := superpose eq21 eq25
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X5)) ◇ X4) ◇ X5) = (X3 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) := superpose eq11 eq11
  have eq31 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ X0)) = (((X0 ◇ X2) ◇ X4) ◇ X3) := superpose eq10 eq11
  have eq34 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) = ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) := superpose eq10 eq11
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X1) = (((X3 ◇ X0) ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq11 eq11
  have eq37 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq11 eq10
  have eq38 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X0)) = X1 := superpose eq11 eq8
  have eq44 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) = X4 := superpose eq11 eq8
  have eq46 (X0 X1 X2 X4 : G) : ((X2 ◇ X0) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = X4 := superpose eq21 eq44
  have eq49 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X5)) ◇ X4) ◇ X5) = ((X2 ◇ X4) ◇ (X0 ◇ X1)) := superpose eq11 eq29
  have eq50 (X0 X1 X2 X4 : G) : ((X2 ◇ X4) ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ (X4 ◇ X1)) := superpose eq21 eq49
  have eq51 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X2))) = (X1 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq8 eq26
  have eq58 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0)) = X3 := superpose eq26 eq26
  have eq108 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) = (((X4 ◇ X0) ◇ X3) ◇ (X5 ◇ (X2 ◇ (X1 ◇ X5)))) := superpose eq10 eq21
  have eq110 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5)) = (((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇ X3) := superpose eq21 eq21
  have eq116 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X5))) ◇ X1))) = (((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ X5) := superpose eq21 eq21
  have eq120 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0))) := superpose eq38 eq21
  have eq126 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X4) ◇ (X2 ◇ (X0 ◇ X3))) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq21 eq11
  have eq127 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X3))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq21 eq26
  have eq132 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X4) ◇ ((X2 ◇ (X0 ◇ X5)) ◇ X1)) = (X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq21 eq11
  have eq133 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X4)) ◇ X1) = (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X3))) := superpose eq21 eq26
  have eq145 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X4) ◇ ((X2 ◇ (X0 ◇ X5)) ◇ X1)) = (((X1 ◇ X2) ◇ X4) ◇ X0) := superpose eq11 eq132
  have eq162 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = (X3 ◇ (((X3 ◇ X4) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X5)) := superpose eq11 eq24
  have eq166 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X4)) = (X1 ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) ◇ X4)) := superpose eq10 eq24
  have eq243 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X4 ◇ X0))) = (X0 ◇ ((X2 ◇ X4) ◇ X1)) := superpose eq24 eq37
  have eq266 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X1) ◇ (X0 ◇ X2)))) = ((X0 ◇ X3) ◇ X4) := superpose eq37 eq21
  have eq489 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X3))) ◇ X1) = ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq21 eq46
  have eq499 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) := superpose eq21 eq46
  have eq506 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X4) ◇ X3) = (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ (X4 ◇ X0)) := superpose eq46 eq11
  have eq649 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X2)) ◇ (X5 ◇ (X1 ◇ X3))) = ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq50 eq50
  have eq651 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X2 ◇ (X0 ◇ X4)) ◇ X1)) ◇ (X5 ◇ X4)) = ((X3 ◇ X5) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq21 eq50
  have eq656 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X5 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X4)))) = ((X3 ◇ X5) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq50
  have eq745 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X3) ◇ X5) ◇ (X0 ◇ X2)) = (X4 ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4))) := superpose eq50 eq11
  have eq770 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X3) ◇ X5) ◇ (X0 ◇ X2)) = (((X2 ◇ X3) ◇ X5) ◇ (X0 ◇ X1)) := superpose eq11 eq745
  have eq1419 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ ((X0 ◇ X2) ◇ X4))) = ((X1 ◇ X5) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq50 eq12
  have eq1422 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ (((X2 ◇ (X0 ◇ (X5 ◇ X6))) ◇ X1) ◇ X3))) = ((X5 ◇ X4) ◇ (X6 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq21 eq12
  have eq1481 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X6)) = ((X4 ◇ X5) ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X6)) := superpose eq12 eq50
  have eq1587 (X0 X1 X2 X3 X5 X6 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X6)) = (((X6 ◇ X1) ◇ X5) ◇ X3) := superpose eq145 eq1481
  have eq1617 (X0 X1 X2 X4 X5 X6 : G) : ((X5 ◇ X4) ◇ (X6 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X1 ◇ X4) ◇ (X2 ◇ (X0 ◇ (X5 ◇ X6)))) := superpose eq11 eq1422
  have eq1619 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X5) ◇ X0) = ((X1 ◇ X5) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq11 eq1419
  have eq1774 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X1)) = (X0 ◇ ((X5 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq46 eq19
  have eq1787 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X0))) = (X0 ◇ ((X5 ◇ (X3 ◇ X1)) ◇ X4)) := superpose eq24 eq19
  have eq1867 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ (X5 ◇ X6)) = (((X6 ◇ X0) ◇ X5) ◇ ((X4 ◇ (X2 ◇ X1)) ◇ X3)) := superpose eq19 eq21
  have eq3345 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X5 ◇ X6)) = (((X6 ◇ (X3 ◇ X1)) ◇ X5) ◇ X4) := superpose eq12 eq31
  have eq3377 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X4 ◇ (X5 ◇ (X6 ◇ X4))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((((X1 ◇ X3) ◇ X5) ◇ (X0 ◇ X2)) ◇ X6) := superpose eq50 eq31
  have eq3388 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X4 ◇ (X5 ◇ X3))) ◇ ((X0 ◇ X1) ◇ X2)) = ((((X1 ◇ ((X2 ◇ X0) ◇ X6)) ◇ X4) ◇ X6) ◇ X5) := superpose eq11 eq31
  have eq3574 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ (X5 ◇ X3))) ◇ ((X0 ◇ X1) ◇ X2)) = (((X2 ◇ X0) ◇ (X4 ◇ X1)) ◇ X5) := superpose eq21 eq3388
  have eq3583 (X0 X1 X2 X3 X5 X6 : G) : ((((X1 ◇ X3) ◇ X5) ◇ (X0 ◇ X2)) ◇ X6) = ((((X2 ◇ X3) ◇ X5) ◇ (X0 ◇ X1)) ◇ X6) := superpose eq31 eq3377
  have eq3594 (X1 X3 X4 X5 X6 : G) : (((X6 ◇ (X3 ◇ X1)) ◇ X5) ◇ X4) = (((X6 ◇ (X3 ◇ X4)) ◇ X5) ◇ X1) := superpose eq1587 eq3345
  have eq3646 (X0 X1 X2 X4 X5 : G) : (((X2 ◇ X0) ◇ (X4 ◇ X1)) ◇ X5) = (((X2 ◇ X4) ◇ (X0 ◇ X1)) ◇ X5) := superpose eq31 eq3574
  have eq4165 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X6 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X5) = ((X0 ◇ ((X4 ◇ (X1 ◇ (X3 ◇ X4))) ◇ (X5 ◇ X6))) ◇ X2) := superpose eq31 eq34
  have eq4174 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4) = ((((X2 ◇ X0) ◇ X3) ◇ (X3 ◇ (X4 ◇ X5))) ◇ X1) := superpose eq11 eq34
  have eq4300 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0)) := superpose eq34 eq9
  have eq4331 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X2 ◇ (X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) ◇ (X6 ◇ X7)) = (((X7 ◇ X5) ◇ X6) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0)))) := superpose eq34 eq31
  have eq4345 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0)))) ◇ (X6 ◇ X2)) = ((X5 ◇ X6) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) := superpose eq34 eq50
  have eq4400 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X7 ◇ X5) ◇ X6) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0)))) = ((X4 ◇ X0) ◇ ((X5 ◇ ((X6 ◇ X7) ◇ X2)) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq489 eq4331
  have eq4420 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) := superpose eq489 eq4300
  have eq4497 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4) = ((X5 ◇ ((X0 ◇ X4) ◇ X2)) ◇ X1) := superpose eq243 eq4174
  have eq4506 (X0 X1 X2 X3 X5 X6 : G) : ((X6 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X5) = ((X0 ◇ (((X6 ◇ X1) ◇ X5) ◇ X3)) ◇ X2) := superpose eq31 eq4165
  have eq4602 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))))))))) := superpose eq1617 eq4420
  have eq4672 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ sK1)))))) := superpose eq489 eq4602
  have eq4698 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ sK1)))))) := superpose eq1617 eq4672
  have eq4712 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := superpose eq126 eq4698
  have eq4720 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1))))) := superpose eq1787 eq4712
  have eq4725 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := superpose eq126 eq4720
  have eq4729 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)))) := superpose eq1787 eq4725
  have eq4733 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := superpose eq126 eq4729
  have eq4737 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := superpose eq649 eq4733
  have eq4741 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((((((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK1)))) := superpose eq31 eq4737
  have eq4745 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((((((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK1) := superpose eq266 eq4741
  have eq4749 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((((((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK0) := superpose eq3594 eq4745
  have eq4753 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((((((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK0) := superpose eq3646 eq4749
  have eq4757 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) ◇ sK0) ◇ sK0) := superpose eq3583 eq4753
  have eq4761 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1))) := superpose eq110 eq4757
  have eq4765 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1))) := superpose eq649 eq4761
  have eq4769 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := superpose eq126 eq4765
  have eq4773 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := superpose eq649 eq4769
  have eq4777 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ ((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK1)))))))) := superpose eq126 eq4773
  have eq4781 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ ((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK1))) ◇ sK0))) := superpose eq120 eq4777
  have eq4785 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ ((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK0))) ◇ sK0))) := superpose eq1774 eq4781
  have eq4789 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ ((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))))) := superpose eq4497 eq4785
  have eq4793 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0))))) := superpose eq649 eq4789
  have eq4797 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)))))))) := superpose eq126 eq4793
  have eq4801 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ ((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))))))))) := superpose eq1619 eq4797
  have eq4805 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))))))))) := superpose eq126 eq4801
  have eq4809 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0))))) := superpose eq499 eq4805
  have eq4813 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))))))) ◇ (sK1 ◇ sK0)))) := superpose eq11 eq4809
  have eq4817 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (((((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))))) := superpose eq1774 eq4813
  have eq4821 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) ◇ sK0)))) := superpose eq489 eq4817
  have eq4825 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ ((((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))))) ◇ (sK0 ◇ sK1)) ◇ sK0)) := superpose eq11 eq4821
  have eq4829 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))))) := superpose eq110 eq4825
  have eq4833 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0)))) ◇ sK1))) := superpose eq489 eq4829
  have eq4837 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := superpose eq11 eq4833
  have eq4841 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0))) ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := superpose eq50 eq4837
  have eq4845 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ ((((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))))) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))))) := superpose eq110 eq4841
  have eq4849 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ sK1) ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))))) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))) := superpose eq1867 eq4845
  have eq4853 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))))))))) := superpose eq126 eq4849
  have eq4857 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ ((sK1 ◇ (sK0 ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) := superpose eq489 eq4853
  have eq4861 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK1))))))) := superpose eq126 eq4857
  have eq4865 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)))) := superpose eq243 eq4861
  have eq4869 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK1))))))) := superpose eq126 eq4865
  have eq4873 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)))))))) ◇ (sK0 ◇ sK1))))))) := superpose eq126 eq4869
  have eq4877 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)))))) ◇ (sK1 ◇ sK1)) ◇ sK0))))) := superpose eq1787 eq4873
  have eq4881 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)))))))) := superpose eq110 eq4877
  have eq4885 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))))) ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := superpose eq4345 eq4881
  have eq4889 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) ◇ sK1))))) := superpose eq656 eq4885
  have eq4893 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (((((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) ◇ sK1) ◇ sK0)) ◇ sK1) ◇ sK1)) := superpose eq116 eq4889
  have eq4897 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (((((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0)) := superpose eq3594 eq4893
  have eq4901 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (((sK0 ◇ (((((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0)) := superpose eq4506 eq4897
  have eq4905 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK0 ◇ (((sK0 ◇ (((((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))))) ◇ sK1) ◇ sK0)) := superpose eq110 eq4901
  have eq4909 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ sK0)) := superpose eq166 eq4905
  have eq4913 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((sK1 ◇ sK1) ◇ ((((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := superpose eq506 eq4909
  have eq4917 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) := superpose eq651 eq4913
  have eq4921 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ ((((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))))) := superpose eq649 eq4917
  have eq4925 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0))) ◇ sK1))) := superpose eq266 eq4921
  have eq4929 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := superpose eq126 eq4925
  have eq4933 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))))) := superpose eq1774 eq4929
  have eq4937 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK0))))) := superpose eq4345 eq4933
  have eq4941 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ (((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ sK1)))) := superpose eq489 eq4937
  have eq4945 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ sK0)))) := superpose eq127 eq4941
  have eq4949 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK1))))) := superpose eq770 eq4945
  have eq4953 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK0)) ◇ sK0)))))))) := superpose eq126 eq4949
  have eq4957 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0))) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))))))))) := superpose eq656 eq4953
  have eq4961 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK0))) ◇ sK1))))))) := superpose eq489 eq4957
  have eq4965 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))))) := superpose eq126 eq4961
  have eq4969 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ sK0))))) := superpose eq116 eq4965
  have eq4973 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))))))))))) := superpose eq110 eq4969
  have eq4977 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) ◇ ((((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))))) ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0))))))))) := superpose eq1617 eq4973
  have eq4981 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) ◇ (((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (sK1 ◇ sK1)))))))) := superpose eq1867 eq4977
  have eq4985 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ sK1))))))))) := superpose eq126 eq4981
  have eq4989 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1)) ◇ sK0)))))) := superpose eq1787 eq4985
  have eq4993 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1)) ◇ (sK1 ◇ sK1))))))) := superpose eq770 eq4989
  have eq4997 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq126 eq4993
  have eq5001 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)))) ◇ sK0))))))) := superpose eq1787 eq4997
  have eq5005 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0))))))))) := superpose eq4345 eq5001
  have eq5009 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0))))))) := superpose eq1867 eq5005
  have eq5013 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))))))))) := superpose eq4345 eq5009
  have eq5017 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))) ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq126 eq5013
  have eq5021 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq162 eq5017
  have eq5025 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ sK1)) ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))) := superpose eq1617 eq5021
  have eq5029 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))))))) := superpose eq649 eq5025
  have eq5033 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))))))))) := superpose eq1617 eq5029
  have eq5037 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) ◇ sK1) ◇ sK0) ◇ sK1))))) := superpose eq145 eq5033
  have eq5041 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) ◇ sK1)))) := superpose eq11 eq5037
  have eq5045 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (((sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1)))) := superpose eq11 eq5041
  have eq5049 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1))))))) := superpose eq126 eq5045
  have eq5053 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ sK1) ◇ ((sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := superpose eq1617 eq5049
  have eq5057 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))))))))) := superpose eq126 eq5053
  have eq5061 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))))))))) := superpose eq50 eq5057
  have eq5065 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))))))))) := superpose eq649 eq5061
  have eq5069 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (((((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1)))))) := superpose eq116 eq5065
  have eq5073 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ (((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := superpose eq656 eq5069
  have eq5077 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0))))))))) := superpose eq126 eq5073
  have eq5081 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK0))))))) := superpose eq4345 eq5077
  have eq5085 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((((sK1 ◇ sK1) ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))) ◇ (sK1 ◇ sK1))))) := superpose eq108 eq5081
  have eq5089 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))))))))) := superpose eq126 eq5085
  have eq5093 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) ◇ (sK0 ◇ sK0))))))))) := superpose eq1774 eq5089
  have eq5097 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK1)))))))) := superpose eq1867 eq5093
  have eq5101 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) ◇ sK1)))))) := superpose eq11 eq5097
  have eq5105 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) ◇ (sK1 ◇ sK1))))))) := superpose eq126 eq5101
  have eq5109 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))))) := superpose eq116 eq5105
  have eq5113 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK1)))) ◇ sK1)) ◇ sK0))) := superpose eq116 eq5109
  have eq5117 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK1)))))) := superpose eq4497 eq5113
  have eq5121 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ (((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))))) := superpose eq649 eq5117
  have eq5125 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))))))))) := superpose eq126 eq5121
  have eq5129 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0))))) := superpose eq1787 eq5125
  have eq5133 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))))))))) := superpose eq126 eq5129
  have eq5137 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))))))))) := superpose eq649 eq5133
  have eq5141 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))))))) := superpose eq4400 eq5137
  have eq5145 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))))))))) := superpose eq126 eq5141
  have eq5149 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)))))))))) := superpose eq50 eq5145
  have eq5153 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))))))))))) := superpose eq126 eq5149
  have eq5184 (X0 : G) : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ X0))))))))))) := superpose eq51 eq5153
  have eq5223 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) = (X0 ◇ (((X5 ◇ X2) ◇ (X4 ◇ X1)) ◇ (X3 ◇ X5))) := superpose eq58 eq35
  have eq5224 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) = (X0 ◇ (((X0 ◇ X3) ◇ (X5 ◇ X1)) ◇ (X4 ◇ X2))) := superpose eq37 eq35
  have eq5727 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (((X1 ◇ X0) ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ sK0) ◇ X1)))))))))) := superpose eq11 eq5184
  have eq5739 (X0 : G) : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ X0) ◇ (X0 ◇ sK0))) ◇ sK1)))))))) := superpose eq5223 eq5727
  have eq5745 (X0 : G) : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ X0) ◇ (X0 ◇ sK0))) ◇ (sK0 ◇ sK0))))))))) := superpose eq126 eq5739
  have eq5750 (X0 : G) : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ X0) ◇ (X0 ◇ sK0))) ◇ (sK0 ◇ sK0))))))))) := superpose eq649 eq5745
  have eq5752 (X0 : G) : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (((X0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)))))))) := superpose eq133 eq5750
  have eq5753 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) ◇ sK1)))))) := superpose eq5223 eq5752
  have eq5754 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK0)))) := superpose eq11 eq5753
  have eq5755 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0)))) := superpose eq3646 eq5754
  have eq5756 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)))) := superpose eq3583 eq5755
  have eq5757 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (((sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ sK0) ◇ sK1)) := superpose eq116 eq5756
  have eq5758 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ (sK1 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := superpose eq110 eq5757
  have eq5759 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) ◇ sK1) := superpose eq5224 eq5758
  have eq5760 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ (sK0 ◇ sK1)) := superpose eq4497 eq5759
  have eq5761 : ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := superpose eq50 eq5760
  subsumption eq5761 rfl

theorem Equation4157_termDefinableFrom_Equation2316 :
    Law4157.TermDefinableFrom Law2316 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op (M.op (M.op x y) x) y)⟩, ?_, ?_⟩
  · rw [@Law4157.models_iff]
    exact @law4157_of_law2316 G M (Law2316.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (Term.var 1))), rfl⟩

/-- Equation 4154 `x ◇ y = ((y ◇ x) ◇ x) ◇ x` is term-definable from equation 2805 `x = ((y ◇ z) ◇ (z ◇ x)) ◇ y`,
via the term `x □ y := y ◇ ((x ◇ ((y ◇ y) ◇ y)) ◇ x)`. -/
private theorem law4154_of_law2805 [Magma G] (h : Equation2805 G) :
    ∀ x y : G, y ◇ ((x ◇ ((y ◇ y) ◇ y)) ◇ x) = x ◇ (((x ◇ (((x ◇ ((y ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ ((x ◇ x) ◇ x)) ◇ y)))) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (((x ◇ ((y ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ ((x ◇ x) ◇ x)) ◇ y))))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X3 := superpose eq8 eq8
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X2 := superpose eq8 eq8
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ ((X0 ◇ X3) ◇ X2)) = X3 := superpose eq12 eq12
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq8 eq12
  have eq16 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq12
  have eq22 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X3) ◇ (X3 ◇ X1))) = X2 := superpose eq12 eq10
  have eq33 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X3 ◇ X2)) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq10 eq12
  have eq38 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))))) = X3 := superpose eq8 eq15
  have eq44 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ X0)) := superpose eq15 eq15
  have eq46 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) := superpose eq10 eq15
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X1 ◇ X2)) = X3 := superpose eq15 eq8
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X1))) = X3 := superpose eq15 eq12
  have eq191 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq14 eq12
  have eq233 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) = (X2 ◇ (X4 ◇ (X3 ◇ X0))) := superpose eq14 eq16
  have eq234 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := superpose eq15 eq16
  have eq242 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X4 ◇ X0) ◇ X3) ◇ X1)) = (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) := superpose eq14 eq16
  have eq278 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ X4) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq16 eq15
  have eq636 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq24 eq15
  have eq2125 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = (X4 ◇ ((X0 ◇ X5) ◇ (X5 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X4))))) := superpose eq15 eq22
  have eq2437 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = (X4 ◇ ((X0 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X1))) := superpose eq278 eq2125
  have eq3484 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X4 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4)) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq44 eq38
  have eq3490 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (X3 ◇ (((X4 ◇ X2) ◇ X5) ◇ (X5 ◇ (X0 ◇ X1)))) := superpose eq44 eq22
  have eq3508 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X2) = (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq44 eq15
  have eq3570 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X4)) := superpose eq3508 eq3490
  have eq5085 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (((X0 ◇ X1) ◇ ((X4 ◇ X3) ◇ (X2 ◇ X5))) ◇ X5) := superpose eq44 eq46
  have eq5151 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = (((X4 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) := superpose eq24 eq46
  have eq7307 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) = (X5 ◇ (X0 ◇ ((X3 ◇ X1) ◇ (X4 ◇ (X2 ◇ X5))))) := superpose eq51 eq22
  have eq8671 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) = ((X1 ◇ X5) ◇ (X5 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X2)))) := superpose eq56 eq33
  have eq8686 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = (((X4 ◇ X0) ◇ X5) ◇ (X5 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq56 eq44
  have eq8701 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) := superpose eq3508 eq8686
  have eq8713 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) := superpose eq278 eq8671
  have eq9755 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X5))) = ((X5 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq56 eq191
  have eq9774 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X1 ◇ ((X5 ◇ X2) ◇ X0))) = (X5 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) := superpose eq191 eq191
  have eq10011 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X4 ◇ (X3 ◇ X5)) ◇ X2) ◇ X0)) = ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X5 ◇ X4)) := superpose eq191 eq51
  have eq11191 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X2) ◇ X4) ◇ ((X1 ◇ X3) ◇ X5)) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) := superpose eq234 eq234
  have eq11229 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X2)) ◇ (X5 ◇ (X1 ◇ X3))) = ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq234 eq234
  have eq11239 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X5) ◇ X0) = ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X5 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X2)))) := superpose eq56 eq234
  have eq11519 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))) ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))))) := superpose eq234 eq9
  have eq11723 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))))))) := superpose eq9755 eq11519
  have eq11871 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X5) ◇ X0) = (X3 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ ((((X4 ◇ X2) ◇ X5) ◇ X0) ◇ X1))) := superpose eq9774 eq11239
  have eq11982 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ ((((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))))))) := superpose eq11191 eq11723
  have eq12037 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ X5) ◇ X0) = ((X1 ◇ (X2 ◇ (((X4 ◇ X2) ◇ X5) ◇ X0))) ◇ X4) := superpose eq2437 eq11871
  have eq12084 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))))) := superpose eq242 eq11982
  have eq12129 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (((((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)))) ◇ sK1) ◇ sK1) := superpose eq7307 eq12084
  have eq12158 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (((sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)))) ◇ sK1) ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq636 eq12129
  have eq12172 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))))))) := superpose eq9755 eq12158
  have eq12180 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))))))) := superpose eq11229 eq12172
  have eq12188 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((((sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ sK0) ◇ sK0))) := superpose eq9774 eq12180
  have eq12196 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))))))) := superpose eq636 eq12188
  have eq12204 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (((((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))))))) := superpose eq9774 eq12196
  have eq12212 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))))))) := superpose eq3508 eq12204
  have eq12220 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))))))) := superpose eq7307 eq12212
  have eq12228 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ sK0)) ◇ (sK1 ◇ sK0)))) := superpose eq3508 eq12220
  have eq12236 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ sK1) ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ sK0)))) := superpose eq11191 eq12228
  have eq12244 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ sK0)) ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK0))))) := superpose eq5151 eq12236
  have eq12251 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (((((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) := superpose eq7307 eq12244
  have eq12257 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((((sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ sK0)) := superpose eq5151 eq12251
  have eq12263 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ ((sK0 ◇ ((((sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ sK0) ◇ sK1)) ◇ sK0)) := superpose eq3570 eq12257
  have eq12269 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ ((((sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ sK0) ◇ sK1)) ◇ (sK0 ◇ sK1))) := superpose eq3484 eq12263
  have eq12275 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)))))))) := superpose eq10011 eq12269
  have eq12281 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (((((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))))) := superpose eq9774 eq12275
  have eq12287 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))))) ◇ sK1) ◇ sK1))) := superpose eq7307 eq12281
  have eq12293 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ sK1))) := superpose eq12037 eq12287
  have eq12299 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1))) ◇ sK1))) := superpose eq8701 eq12293
  have eq12305 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ ((sK1 ◇ (((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := superpose eq5085 eq12299
  have eq12311 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ ((((((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ sK0)) := superpose eq7307 eq12305
  have eq12317 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ ((((((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ sK0) ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ sK0)) := superpose eq8701 eq12311
  have eq12323 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ sK0))) ◇ sK0))) := superpose eq5085 eq12317
  have eq12329 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ sK0))) ◇ sK0))) := superpose eq3570 eq12323
  have eq12335 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ sK1))) ◇ sK0))) := superpose eq636 eq12329
  have eq12341 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK1) ◇ sK0))) ◇ sK1))) := superpose eq8713 eq12335
  have eq12347 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK1))) := superpose eq233 eq12341
  have eq12353 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)))) := superpose eq8713 eq12347
  have eq12359 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))))) := superpose eq10011 eq12353
  have eq12365 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) ◇ sK1))) := superpose eq2437 eq12359
  have eq12371 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := superpose eq191 eq12365
  have eq12377 : (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) := superpose eq3570 eq12371
  subsumption eq12377 rfl

theorem Equation4154_termDefinableFrom_Equation2805 :
    Law4154.TermDefinableFrom Law2805 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op y (M.op (M.op x (M.op (M.op y y) y)) x)⟩, ?_, ?_⟩
  · rw [@Law4154.models_iff]
    exact @law4154_of_law2805 G M (Law2805.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 1) (tm (tm (Term.var 0) (tm (tm (Term.var 1) (Term.var 1)) (Term.var 1))) (Term.var 0))), rfl⟩

/-- Equation 3961 `x ◇ y = (y ◇ (y ◇ x)) ◇ x` is term-definable from equation 2805 `x = ((y ◇ z) ◇ (z ◇ x)) ◇ y`,
via the term `x □ y := (y ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ x)`. -/
private theorem law3961_of_law2805 [Magma G] (h : Equation2805 G) :
    ∀ x y : G, (y ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ x) = (x ◇ x) ◇ ((x ◇ (x ◇ ((((x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y))) ◇ ((((x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ y)) ◇ y)))) ◇ ((((x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y))) ◇ ((((x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ y)) ◇ y))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X3 := superpose eq8 eq8
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X2 := superpose eq8 eq8
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0)))) = X3 := superpose eq8 eq12
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ ((X0 ◇ X3) ◇ X2)) = X3 := superpose eq12 eq12
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq8 eq12
  have eq16 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq12
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = (((X3 ◇ X2) ◇ X0) ◇ X3) := superpose eq12 eq8
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X2) ◇ X3)) ◇ X1) = X3 := superpose eq12 eq8
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ ((X2 ◇ X4) ◇ (X4 ◇ X1))) := superpose eq12 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X3) ◇ (X3 ◇ X1))) = X2 := superpose eq12 eq10
  have eq33 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X3 ◇ X2)) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq10 eq12
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X1)) ◇ X4)) ◇ (X1 ◇ (X2 ◇ X0))) = X4 := superpose eq10 eq8
  have eq38 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))))) = X3 := superpose eq8 eq15
  have eq40 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq15 eq15
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X2) ◇ (X3 ◇ X1))) = X3 := superpose eq12 eq15
  have eq44 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ X0)) := superpose eq15 eq15
  have eq46 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) := superpose eq10 eq15
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X1 ◇ X2)) = X3 := superpose eq15 eq8
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X1))) = X3 := superpose eq15 eq12
  have eq191 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq14 eq12
  have eq234 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := superpose eq15 eq16
  have eq242 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X4 ◇ X0) ◇ X3) ◇ X1)) = (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) := superpose eq14 eq16
  have eq278 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ X4) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq16 eq15
  have eq636 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq24 eq15
  have eq1506 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X4 ◇ ((X5 ◇ X2) ◇ X1)) ◇ X6) ◇ X4) = ((X7 ◇ X6) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) ◇ (X5 ◇ X7))) := superpose eq21 eq21
  have eq1508 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ ((X4 ◇ X1) ◇ X2)) ◇ X5) ◇ X3) = ((X6 ◇ X5) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X4 ◇ X6))) := superpose eq17 eq21
  have eq1510 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ ((X4 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X5) ◇ X3) = ((X6 ◇ X5) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X6))) := superpose eq16 eq21
  have eq1545 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ ((X1 ◇ X4) ◇ (X2 ◇ X0))) ◇ X5) ◇ X3) = ((X4 ◇ X5) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq16 eq21
  have eq1773 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X0) ◇ (X5 ◇ (X1 ◇ X4))) := superpose eq16 eq1545
  have eq1793 (X0 X1 X2 X4 X5 X6 : G) : ((X6 ◇ X5) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X6))) = (X1 ◇ (X5 ◇ (X4 ◇ (X2 ◇ X0)))) := superpose eq16 eq1510
  have eq1795 (X0 X1 X2 X4 X5 X6 : G) : ((X6 ◇ X5) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X4 ◇ X6))) = (X2 ◇ (X5 ◇ (X4 ◇ X1))) := superpose eq16 eq1508
  have eq1797 (X0 X1 X2 X3 X5 X6 X7 : G) : ((X7 ◇ X6) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) ◇ (X5 ◇ X7))) = (X1 ◇ (X6 ◇ (X5 ◇ X2))) := superpose eq16 eq1506
  have eq1865 (X0 X1 X2 X3 X5 X6 : G) : (X1 ◇ (X6 ◇ (X5 ◇ X2))) = ((X2 ◇ X3) ◇ (X6 ◇ (X5 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1))))) := superpose eq1793 eq1797
  have eq1944 (X0 X1 X2 X3 X4 X5 : G) : (((X5 ◇ X4) ◇ (X2 ◇ X0)) ◇ X1) = (X3 ◇ ((X4 ◇ (X3 ◇ X5)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq16 eq40
  have eq2125 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = (X4 ◇ ((X0 ◇ X5) ◇ (X5 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X4))))) := superpose eq15 eq22
  have eq2219 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = ((X3 ◇ X2) ◇ ((((X4 ◇ X3) ◇ X1) ◇ X4) ◇ X0)) := superpose eq13 eq22
  have eq2241 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X2) = (((X2 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq22 eq15
  have eq2437 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = (X4 ◇ ((X0 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X1))) := superpose eq278 eq2125
  have eq2604 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X2 ◇ X0)) ◇ X1) = (X3 ◇ ((((X4 ◇ X5) ◇ X3) ◇ X4) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq16 eq41
  have eq3484 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X4 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4)) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq44 eq38
  have eq3490 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (X3 ◇ (((X4 ◇ X2) ◇ X5) ◇ (X5 ◇ (X0 ◇ X1)))) := superpose eq44 eq22
  have eq3508 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X2) = (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq44 eq15
  have eq3570 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X4)) := superpose eq3508 eq3490
  have eq5085 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (((X0 ◇ X1) ◇ ((X4 ◇ X3) ◇ (X2 ◇ X5))) ◇ X5) := superpose eq44 eq46
  have eq7313 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) = (X5 ◇ (X0 ◇ ((X3 ◇ X1) ◇ (X4 ◇ (X2 ◇ X5))))) := superpose eq51 eq22
  have eq8671 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) = ((X1 ◇ X5) ◇ (X5 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X2)))) := superpose eq56 eq33
  have eq8686 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = (((X4 ◇ X0) ◇ X5) ◇ (X5 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq56 eq44
  have eq8701 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) := superpose eq3508 eq8686
  have eq8713 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) := superpose eq278 eq8671
  have eq9755 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X5))) = ((X5 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq56 eq191
  have eq9762 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = ((X5 ◇ (((X4 ◇ X6) ◇ (X6 ◇ X3)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq36 eq191
  have eq9774 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X1 ◇ ((X5 ◇ X2) ◇ X0))) = (X5 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) := superpose eq191 eq191
  have eq9924 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X4) = (X5 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X6) ◇ (X6 ◇ (X4 ◇ (X3 ◇ X5))))) := superpose eq191 eq22
  have eq9956 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X4) = (((X4 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) ◇ (X5 ◇ X3)) := superpose eq191 eq44
  have eq10016 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X4 ◇ (X3 ◇ X5)) ◇ X2) ◇ X0)) = ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X5 ◇ X4)) := superpose eq191 eq51
  have eq10023 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) = (X1 ◇ (((((X4 ◇ X5) ◇ X3) ◇ X4) ◇ X2) ◇ X0)) := superpose eq191 eq18
  have eq10093 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X4) = (X5 ◇ (((X3 ◇ X5) ◇ (X2 ◇ X4)) ◇ (X0 ◇ X1))) := superpose eq3508 eq9924
  have eq10154 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = ((X6 ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X5 ◇ X2)) ◇ X0) ◇ (X4 ◇ X6))) := superpose eq10016 eq9762
  have eq10208 (X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = ((X5 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) := superpose eq1795 eq10154
  have eq11191 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X2) ◇ X4) ◇ ((X1 ◇ X3) ◇ X5)) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) := superpose eq234 eq234
  have eq11221 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X1 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X5)) = (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ X5)) := superpose eq191 eq234
  have eq11472 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ ((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) := superpose eq234 eq9
  have eq11737 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ ((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ ((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) := superpose eq3570 eq11472
  have eq11974 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))) ◇ (((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ (((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK0)))) := superpose eq9755 eq11737
  have eq12071 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((((((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ (sK0 ◇ sK0)))) := superpose eq10016 eq11974
  have eq12112 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq1793 eq12071
  have eq12137 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq234 eq12112
  have eq12147 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ ((((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ ((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq9774 eq12137
  have eq12151 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ ((((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ ((((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq234 eq12147
  have eq12155 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))))))))) := superpose eq7313 eq12151
  have eq12159 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))))))))) := superpose eq9774 eq12155
  have eq12163 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := superpose eq1865 eq12159
  have eq12167 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((((sK0 ◇ sK1) ◇ (((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK0) := superpose eq1944 eq12163
  have eq12171 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ sK1)) ◇ sK0) := superpose eq8701 eq12167
  have eq12175 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ sK1)) := superpose eq636 eq12171
  have eq12179 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (((sK0 ◇ (((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ (sK0 ◇ sK0))) ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) := superpose eq11191 eq12175
  have eq12183 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ (((sK1 ◇ ((sK0 ◇ (((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ (sK0 ◇ sK0))) ◇ sK0)) ◇ sK1) ◇ sK0)) := superpose eq242 eq12179
  have eq12187 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ (((sK0 ◇ ((sK0 ◇ (((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ ((sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ (sK0 ◇ sK0))) ◇ sK0)) ◇ sK1) ◇ sK1)) := superpose eq636 eq12183
  have eq12191 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ (((sK0 ◇ ((sK0 ◇ (((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0) ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) ◇ sK0))) ◇ sK0)) ◇ sK1) ◇ sK1)) := superpose eq11191 eq12187
  have eq12195 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ (((sK0 ◇ ((sK0 ◇ (sK1 ◇ (((sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ sK0)) ◇ sK1) ◇ sK1)) := superpose eq242 eq12191
  have eq12199 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ (((sK0 ◇ ((sK0 ◇ (sK1 ◇ (((sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0)) ◇ sK0) ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) ◇ sK1)) := superpose eq8713 eq12195
  have eq12203 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ (((sK0 ◇ ((sK0 ◇ (sK1 ◇ (((sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0)) ◇ sK0) ◇ sK0))) ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1)) := superpose eq8713 eq12199
  have eq12207 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ ((sK0 ◇ (sK1 ◇ (((sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0)) ◇ sK0) ◇ sK0))) ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) := superpose eq3570 eq12203
  have eq12211 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ (((sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0)) ◇ sK0) ◇ sK0))) ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) := superpose eq8701 eq12207
  have eq12215 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ (((sK0 ◇ (sK1 ◇ (((sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0)) ◇ sK0) ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)) := superpose eq3570 eq12211
  have eq12219 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (((sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0)) ◇ sK0) ◇ sK0)) ◇ sK1)) ◇ sK1)) ◇ sK1)) := superpose eq8701 eq12215
  have eq12223 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))))))) ◇ sK1)) ◇ sK1)) ◇ sK1)) := superpose eq16 eq12219
  have eq12227 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))))))) ◇ sK1)) ◇ sK1)) ◇ sK1)) := superpose eq3570 eq12223
  have eq12231 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))))) ◇ sK1)) ◇ sK1)) := superpose eq8713 eq12227
  have eq12235 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (sK0 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1))))) ◇ sK1)) := superpose eq8713 eq12231
  have eq12239 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1)))) := superpose eq8713 eq12235
  have eq12243 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK1 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0)))) := superpose eq9755 eq12239
  have eq12247 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ (sK0 ◇ sK0)))) := superpose eq10016 eq12243
  have eq12251 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (((((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := superpose eq10208 eq12247
  have eq12255 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (((((sK0 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK0) ◇ (((sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := superpose eq11191 eq12251
  have eq12259 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (((sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))))))) := superpose eq10208 eq12255
  have eq12263 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ ((((((sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))))) ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK0))) := superpose eq242 eq12259
  have eq12267 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (((sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))))))) := superpose eq636 eq12263
  have eq12271 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (((sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0) ◇ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))))))) := superpose eq234 eq12267
  have eq12275 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq9774 eq12271
  have eq12279 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq234 eq12275
  have eq12283 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))))))))) := superpose eq9774 eq12279
  have eq12287 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1))))))))) := superpose eq11191 eq12283
  have eq12291 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))))))) := superpose eq10023 eq12287
  have eq12295 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))))) ◇ (sK0 ◇ sK1))))))) := superpose eq191 eq12291
  have eq12299 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ ((((sK0 ◇ sK1) ◇ sK1) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))))) ◇ sK0)))))) := superpose eq9774 eq12295
  have eq12303 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))))) ◇ (sK0 ◇ sK1))))))) := superpose eq636 eq12299
  have eq12307 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK0) ◇ ((sK1 ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))) ◇ sK1))))))) := superpose eq11191 eq12303
  have eq12311 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (((sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK0) ◇ ((sK1 ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))))))) := superpose eq8713 eq12307
  have eq12315 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK0) ◇ (sK1 ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1))))))) := superpose eq7313 eq12311
  have eq12319 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq1773 eq12315
  have eq12323 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((((sK0 ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) ◇ sK1) ◇ sK1)))) := superpose eq242 eq12319
  have eq12327 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) ◇ sK1) ◇ (sK0 ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq636 eq12323
  have eq12331 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ (((((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))))))))) := superpose eq234 eq12327
  have eq12335 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ ((((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)))) ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1)))))))) := superpose eq242 eq12331
  have eq12339 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))))) := superpose eq2604 eq12335
  have eq12343 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)))) ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))))))) := superpose eq7313 eq12339
  have eq12347 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)))))))) := superpose eq10208 eq12343
  have eq12351 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((((sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))))) ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0))) := superpose eq242 eq12347
  have eq12355 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ ((((sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))))) ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0))) := superpose eq3570 eq12351
  have eq12359 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ ((((sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))))) ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK0))) := superpose eq8701 eq12355
  have eq12363 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)))))))) := superpose eq636 eq12359
  have eq12367 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1)) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)))))))) := superpose eq11191 eq12363
  have eq12371 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1))))))) := superpose eq10208 eq12367
  have eq12375 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1)) ◇ sK0)))) := superpose eq242 eq12371
  have eq12379 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((((sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1) ◇ sK1)) ◇ sK0)))) := superpose eq8701 eq12375
  have eq12383 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (((sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1))))))) := superpose eq636 eq12379
  have eq12387 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (((sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1)) ◇ sK0) ◇ ((((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ sK1))))))) := superpose eq11191 eq12383
  have eq12391 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))) ◇ ((sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1)) ◇ sK0)) ◇ sK0))) := superpose eq7313 eq12387
  have eq12395 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1))) ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ sK0))) := superpose eq8701 eq12391
  have eq12399 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1))) ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK0)) ◇ sK1))) := superpose eq636 eq12395
  have eq12403 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ ((((((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) ◇ sK0) ◇ ((sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1)) ◇ sK0)) ◇ sK1))) := superpose eq11221 eq12399
  have eq12407 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ ((sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))))))) := superpose eq242 eq12403
  have eq12411 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK0)) := superpose eq10093 eq12407
  have eq12415 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ (((sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK1)) := superpose eq636 eq12411
  have eq12419 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1)) ◇ sK0)) ◇ sK1))) := superpose eq5085 eq12415
  have eq12423 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1)) ◇ sK0)))) ◇ sK1) := superpose eq2437 eq12419
  have eq12427 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ ((sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ sK1)) ◇ sK0)) := superpose eq8713 eq12423
  have eq12431 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK1)) ◇ sK0)) := superpose eq3570 eq12427
  have eq12435 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) ◇ ((sK0 ◇ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK1)) ◇ sK0)) := superpose eq8701 eq12431
  have eq12439 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK1)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK1)))) := superpose eq3484 eq12435
  have eq12443 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) ◇ (((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK0) ◇ (sK1 ◇ sK0)))) := superpose eq9755 eq12439
  have eq12447 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK0))) ◇ sK0) ◇ sK0))) := superpose eq10016 eq12443
  have eq12451 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK0))) ◇ sK0) ◇ (sK1 ◇ sK0)))) := superpose eq636 eq12447
  have eq12455 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK0))) ◇ sK0) ◇ (sK1 ◇ sK0)))) := superpose eq3570 eq12451
  have eq12459 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK1) ◇ sK0))) := superpose eq2241 eq12455
  have eq12463 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ sK1))) ◇ sK1) ◇ sK1))) := superpose eq636 eq12459
  have eq12467 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) ◇ sK1))) ◇ sK1) ◇ sK1))) := superpose eq3570 eq12463
  have eq12471 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK1) ◇ sK1))) := superpose eq8701 eq12467
  have eq12475 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ◇ sK1))) ◇ sK1) ◇ sK1))) := superpose eq3570 eq12471
  have eq12479 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((((sK1 ◇ sK0) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ sK1))) := superpose eq191 eq12475
  have eq12483 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ (((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ sK1))) := superpose eq2219 eq12479
  have eq12487 : ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0)) := superpose eq9956 eq12483
  have eq12491 : (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0)) ≠ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0)) := superpose eq3570 eq12487
  subsumption eq12491 rfl

theorem Equation3961_termDefinableFrom_Equation2805 :
    Law3961.TermDefinableFrom Law2805 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op y y) (M.op (M.op y (M.op y x)) x)⟩, ?_, ?_⟩
  · rw [@Law3961.models_iff]
    exact @law3961_of_law2805 G M (Law2805.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (tm (tm (Term.var 1) (tm (Term.var 1) (Term.var 0))) (Term.var 0))), rfl⟩

/-- Equation 3954 `x ◇ y = (y ◇ (x ◇ y)) ◇ x` is term-definable from equation 2805 `x = ((y ◇ z) ◇ (z ◇ x)) ◇ y`,
via the term `x □ y := x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)`. -/
private theorem law3954_of_law2805 [Magma G] (h : Equation2805 G) :
    ∀ x y : G, x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x) = (y ◇ (((x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)) ◇ (((x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x))) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)))) ◇ y)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ (((x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)) ◇ (((x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x))) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)))) ◇ y))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X3 := superpose eq8 eq8
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X2 := superpose eq8 eq8
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ ((X0 ◇ X3) ◇ X2)) = X3 := superpose eq12 eq12
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq8 eq12
  have eq16 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq12
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = (((X3 ◇ X2) ◇ X0) ◇ X3) := superpose eq12 eq8
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ ((X2 ◇ X4) ◇ (X4 ◇ X1))) := superpose eq12 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X3) ◇ (X3 ◇ X1))) = X2 := superpose eq12 eq10
  have eq33 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X3 ◇ X2)) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq10 eq12
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X1)) ◇ X4)) ◇ (X1 ◇ (X2 ◇ X0))) = X4 := superpose eq10 eq8
  have eq38 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))))) = X3 := superpose eq8 eq15
  have eq44 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ X0)) := superpose eq15 eq15
  have eq46 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) := superpose eq10 eq15
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X1 ◇ X2)) = X3 := superpose eq15 eq8
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X1))) = X3 := superpose eq15 eq12
  have eq191 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq14 eq12
  have eq234 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := superpose eq15 eq16
  have eq242 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X4 ◇ X0) ◇ X3) ◇ X1)) = (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) := superpose eq14 eq16
  have eq278 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ X4) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq16 eq15
  have eq335 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X1) = (X0 ◇ ((X2 ◇ X4) ◇ X3)) := superpose eq14 eq17
  have eq636 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq24 eq15
  have eq1508 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ ((X4 ◇ X1) ◇ X2)) ◇ X5) ◇ X3) = ((X6 ◇ X5) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X4 ◇ X6))) := superpose eq17 eq21
  have eq1545 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ ((X1 ◇ X4) ◇ (X2 ◇ X0))) ◇ X5) ◇ X3) = ((X4 ◇ X5) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq16 eq21
  have eq1773 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X0) ◇ (X5 ◇ (X1 ◇ X4))) := superpose eq16 eq1545
  have eq1795 (X0 X1 X2 X4 X5 X6 : G) : ((X6 ◇ X5) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X4 ◇ X6))) = (X2 ◇ (X5 ◇ (X4 ◇ X1))) := superpose eq16 eq1508
  have eq2125 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = (X4 ◇ ((X0 ◇ X5) ◇ (X5 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X4))))) := superpose eq15 eq22
  have eq2437 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = (X4 ◇ ((X0 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X1))) := superpose eq278 eq2125
  have eq3484 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X4 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4)) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq44 eq38
  have eq3490 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (X3 ◇ (((X4 ◇ X2) ◇ X5) ◇ (X5 ◇ (X0 ◇ X1)))) := superpose eq44 eq22
  have eq3508 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X2) = (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq44 eq15
  have eq3520 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) ◇ X5) ◇ X2) = ((X6 ◇ X5) ◇ ((X0 ◇ X1) ◇ ((X4 ◇ X3) ◇ X6))) := superpose eq44 eq21
  have eq3549 (X0 X1 X3 X4 X5 X6 : G) : ((X6 ◇ X5) ◇ ((X0 ◇ X1) ◇ ((X4 ◇ X3) ◇ X6))) = (X4 ◇ (X5 ◇ (X1 ◇ (X3 ◇ X0)))) := superpose eq16 eq3520
  have eq3570 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X4)) := superpose eq3508 eq3490
  have eq5085 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = (((X0 ◇ X1) ◇ ((X4 ◇ X3) ◇ (X2 ◇ X5))) ◇ X5) := superpose eq44 eq46
  have eq5151 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = (((X4 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) := superpose eq24 eq46
  have eq5198 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X4) = (X5 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X5))))) := superpose eq46 eq22
  have eq7313 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) = (X5 ◇ (X0 ◇ ((X3 ◇ X1) ◇ (X4 ◇ (X2 ◇ X5))))) := superpose eq51 eq22
  have eq8671 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) = ((X1 ◇ X5) ◇ (X5 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X2)))) := superpose eq56 eq33
  have eq8686 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = (((X4 ◇ X0) ◇ X5) ◇ (X5 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq56 eq44
  have eq8690 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X4) = (((X4 ◇ X5) ◇ (X5 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) := superpose eq56 eq46
  have eq8701 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) := superpose eq3508 eq8686
  have eq8713 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) := superpose eq278 eq8671
  have eq9755 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X5))) = ((X5 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq56 eq191
  have eq9762 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = ((X5 ◇ (((X4 ◇ X6) ◇ (X6 ◇ X3)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq36 eq191
  have eq9774 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X1 ◇ ((X5 ◇ X2) ◇ X0))) = (X5 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) := superpose eq191 eq191
  have eq9924 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X4) = (X5 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X6) ◇ (X6 ◇ (X4 ◇ (X3 ◇ X5))))) := superpose eq191 eq22
  have eq9965 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X4 ◇ X2) ◇ X0)) = ((X3 ◇ (X4 ◇ X5)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X5 ◇ X3))) := superpose eq191 eq56
  have eq10016 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X4 ◇ (X3 ◇ X5)) ◇ X2) ◇ X0)) = ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X5 ◇ X4)) := superpose eq191 eq51
  have eq10093 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X4) = (X5 ◇ (((X3 ◇ X5) ◇ (X2 ◇ X4)) ◇ (X0 ◇ X1))) := superpose eq3508 eq9924
  have eq10154 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = ((X6 ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X5 ◇ X2)) ◇ X0) ◇ (X4 ◇ X6))) := superpose eq10016 eq9762
  have eq10208 (X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = ((X5 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) := superpose eq1795 eq10154
  have eq11191 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X2) ◇ X4) ◇ ((X1 ◇ X3) ◇ X5)) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) := superpose eq234 eq234
  have eq11477 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)))) := superpose eq234 eq9
  have eq11637 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ X3)) = ((X0 ◇ X2) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4))) := superpose eq234 eq191
  have eq11743 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ ((((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) := superpose eq10016 eq11477
  have eq11984 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ ((((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0)) := superpose eq10016 eq11743
  have eq12085 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ ((((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ sK0)) ◇ sK0)) := superpose eq3570 eq11984
  have eq12130 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK0 ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ sK0)))) ◇ sK1) ◇ sK1)) := superpose eq10016 eq12085
  have eq12159 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK1 ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ sK0)))) ◇ sK1) ◇ sK0)) := superpose eq636 eq12130
  have eq12173 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK1 ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ sK1))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ sK0)) ◇ sK0)) := superpose eq8713 eq12159
  have eq12181 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ sK1)) ◇ sK0)) ◇ sK0)) := superpose eq8701 eq12173
  have eq12189 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ ((((sK1 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ sK1)))) ◇ sK0) ◇ sK1)) ◇ sK0)) := superpose eq10016 eq12181
  have eq12197 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ sK1)))) ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))) := superpose eq242 eq12189
  have eq12205 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ sK1)))) ◇ sK0)) ◇ sK1)) ◇ sK1) := superpose eq10093 eq12197
  have eq12213 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ sK1)))) ◇ sK0)) ◇ sK1)) ◇ sK1) := superpose eq3570 eq12205
  have eq12221 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ sK1))) ◇ sK1)) ◇ sK1) := superpose eq8713 eq12213
  have eq12229 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))))) ◇ sK1)) ◇ sK1) := superpose eq5085 eq12221
  have eq12237 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))))) ◇ sK1) := superpose eq8713 eq12229
  have eq12245 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) := superpose eq8713 eq12237
  have eq12253 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ (((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1))) := superpose eq9755 eq12245
  have eq12261 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ (((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0))) := superpose eq10208 eq12253
  have eq12269 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ (((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0))) := superpose eq3570 eq12261
  have eq12277 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK1 ◇ (sK1 ◇ sK0)) ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1)) ◇ ((((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) := superpose eq11191 eq12269
  have eq12285 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)))) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) := superpose eq10016 eq12277
  have eq12293 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1))))))))) := superpose eq3549 eq12285
  have eq12301 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)))))))) := superpose eq9774 eq12293
  have eq12309 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (((((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ sK1)) ◇ sK0)))))) := superpose eq2437 eq12301
  have eq12317 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (((((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ sK1))))) := superpose eq191 eq12309
  have eq12325 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))))))) := superpose eq636 eq12317
  have eq12333 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((((((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))))) := superpose eq9774 eq12325
  have eq12341 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((((((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1) ◇ sK0) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK0)))))) := superpose eq8701 eq12333
  have eq12349 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))))))))) := superpose eq5085 eq12341
  have eq12357 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((((sK0 ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1) ◇ sK1))))) := superpose eq7313 eq12349
  have eq12365 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1) ◇ (sK0 ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ sK1))))))) := superpose eq636 eq12357
  have eq12373 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))))))))) := superpose eq1773 eq12365
  have eq12381 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (((sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))))))))) := superpose eq234 eq12373
  have eq12389 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) ◇ ((((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))))))) := superpose eq11637 eq12381
  have eq12397 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK1))) ◇ sK0)))) := superpose eq5198 eq12389
  have eq12405 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ (sK0 ◇ sK1)))) ◇ sK0)))) := superpose eq3484 eq12397
  have eq12413 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ (sK0 ◇ sK1)))) ◇ sK0)))) := superpose eq3570 eq12405
  have eq12421 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK0))) ◇ (sK0 ◇ sK1))))) := superpose eq8713 eq12413
  have eq12429 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ (((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)))) ◇ sK0)) ◇ sK1))))) := superpose eq234 eq12421
  have eq12437 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))))) ◇ sK1))))) := superpose eq335 eq12429
  have eq12445 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))))) ◇ sK1))))) := superpose eq3570 eq12437
  have eq12453 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))))))) := superpose eq8713 eq12445
  have eq12461 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ (((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK1) ◇ sK0))))))) := superpose eq9755 eq12453
  have eq12469 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))))))))) := superpose eq3549 eq12461
  have eq12477 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK0)) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))))) := superpose eq10093 eq12469
  have eq12485 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK0))) ◇ ((sK1 ◇ sK1) ◇ sK1)))) := superpose eq191 eq12477
  have eq12493 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK0)))) ◇ sK1)) := superpose eq191 eq12485
  have eq12501 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK0))) := superpose eq8713 eq12493
  have eq12509 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)))) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK1))) := superpose eq242 eq12501
  have eq12517 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK1))) := superpose eq3570 eq12509
  have eq12525 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ (((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1))) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK1))) := superpose eq8701 eq12517
  have eq12533 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1))) ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0))) ◇ sK0))) := superpose eq636 eq12525
  have eq12541 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ ((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)) ◇ sK1)) ◇ sK1)))) := superpose eq5085 eq12533
  have eq12549 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)) ◇ sK1)) ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := superpose eq191 eq12541
  have eq12557 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)) ◇ sK1))) := superpose eq5151 eq12549
  have eq12565 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)))) ◇ (sK0 ◇ sK1)) := superpose eq8690 eq12557
  have eq12573 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)) := superpose eq8713 eq12565
  have eq12581 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK1 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := superpose eq3484 eq12573
  have eq12589 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := superpose eq2437 eq12581
  have eq12597 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) := superpose eq10016 eq12589
  have eq12605 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0)) := superpose eq242 eq12597
  have eq12613 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) ◇ sK0)) := superpose eq3570 eq12605
  have eq12621 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ (((sK1 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ sK0)) := superpose eq8701 eq12613
  have eq12629 : (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ≠ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) := superpose eq9965 eq12621
  subsumption eq12629 rfl

theorem Equation3954_termDefinableFrom_Equation2805 :
    Law3954.TermDefinableFrom Law2805 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op x (M.op (M.op y (M.op (M.op y y) y)) x)⟩, ?_, ?_⟩
  · rw [@Law3954.models_iff]
    exact @law3954_of_law2805 G M (Law2805.models_iff.mp hGL)
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (tm (Term.var 1) (Term.var 1)) (Term.var 1))) (Term.var 0))), rfl⟩

/-- Equation 3758 `x ◇ y = (y ◇ y) ◇ (x ◇ x)` is term-definable from equation 3751 `x ◇ y = (y ◇ x) ◇ (y ◇ x)`,
via the term `x □ y := (x ◇ x) ◇ (y ◇ y)`. -/
private theorem law3758_of_law3751 [Magma G] (h : Equation3751 G) :
    ∀ x y : G, (x ◇ x) ◇ (y ◇ y) = (((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ≠ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq8 eq8
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq10 eq8
  have eq33 : ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ≠ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose eq10 eq9
  have eq37 : ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ≠ ((((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := superpose eq8 eq33
  have eq41 : ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := superpose eq30 eq37
  have eq45 : ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := superpose eq8 eq41
  have eq49 : ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq8 eq45
  subsumption eq49 rfl

theorem Equation3758_termDefinableFrom_Equation3751 :
    Law3758.TermDefinableFrom Law3751 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op y y)⟩, ?_, ?_⟩
  · rw [@Law3758.models_iff]
    exact @law3758_of_law3751 G M (Law3751.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), rfl⟩

/-- Equation 43 `x ◇ y = y ◇ x` is term-definable from equation 4482 `x ◇ (y ◇ y) = (y ◇ y) ◇ x`,
via the term `x □ y := (x ◇ x) ◇ (y ◇ y)`. -/
private theorem law43_of_law4482 [Magma G] (h : Equation4482 G) :
    ∀ x y : G, (x ◇ x) ◇ (y ◇ y) = (y ◇ y) ◇ (x ◇ x) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq9 : ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq8 eq9
  subsumption eq11 rfl

theorem Equation43_termDefinableFrom_Equation4482 :
    Law43.TermDefinableFrom Law4482 := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op (M.op x x) (M.op y y)⟩, ?_, ?_⟩
  · rw [@Law43.models_iff]
    exact @law43_of_law4482 G M (Law4482.models_iff.mp hGL)
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), rfl⟩

end Law.MagmaLaw
