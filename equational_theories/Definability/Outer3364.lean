import equational_theories.Definability.OuterIterate
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Source 3364: cells landed by an idempotent iterate applied outside the defining term

The unary term (xx) is iterated outside the defining term. `OuterIterate.lean` names the two
families of iterates the device can reach -- `v^[k] = u^[N k]` and `e ∘ v^[k] = u^[N k + N + 1]` --
and each cell below picks the wrapper and the base term that its target needs.

No endomorphism fact is needed at all. `termDefinableOnMagma_of_iterate_pair` takes an arbitrary
`UTerm G`, and `Function.exists_isIdempotentIterate` asks only that the carrier be finite, so the
unary term below is iterated without ever distributing over `◇`. That widens the pool from the
handful of certified endomorphisms to every unary term the source has.
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

/-- The magma operation as a one-variable term: `tm` at the other arity. -/
private abbrev tm1 (a b : (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 1)) :
    (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 1) :=
  Functions.apply₂ (Sum.inl ()) a b


/-- Equation 332 `x ◇ y = y ◇ (x ◇ x)` is term-definable from equation 3364 over finite magmas, via the term
`x □ y := (x ◇ y)` with `u a = (a ◇ a)`
taken at x at u^[2N+1], y at u^[2N+1]. -/
private theorem aux3364_332 [Magma G] (h : Equation3364 G) (e v : G → G) (w : G → G → G)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huv : ∀ a : G, ((v a) ◇ (v a)) = e a)
    (hvu : ∀ a : G, v (a ◇ a) = e a)
    (hw : ∀ a b : G, w a b = ((e (v a)) ◇ (e (v b))))
    (x y : G) :
    (w x y) =
      (w y (w x x)) := by
  by_contra nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq12 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq13 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq14 (X0 : G) : (e X0) = ((v X0) ◇ (v X0)) := mod_symm (huv ..)
  have eq16 (X0 X1 : G) : (w X0 X1) = ((e (v X0)) ◇ (e (v X1))) := mod_symm (hw ..)
  have eq17 : (w x y) ≠ (w y (w x x)) := mod_symm nh
  have eq21 (X0 : G) : (e (e X0)) = ((e (v X0)) ◇ (e (v X0))) := by first | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14) | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13)
  have eq24 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq16 eq21 | exact mod_symm (superpose eq16 eq21) | exact superpose eq21 eq16 | exact mod_symm (superpose eq21 eq16)
  have eq25 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq12 eq24 | exact mod_symm (superpose eq12 eq24) | exact superpose eq24 eq12 | exact mod_symm (superpose eq24 eq12)
  have eq26 (X0 X1 : G) : ((v X0) ◇ X1) = (X1 ◇ ((v X0) ◇ (e X0))) := by first | exact superpose eq14 eq11 | exact mod_symm (superpose eq14 eq11) | exact superpose eq11 eq14 | exact mod_symm (superpose eq11 eq14)
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by first | exact superpose eq11 eq11 | exact mod_symm (superpose eq11 eq11) | exact superpose eq11 eq11 | exact mod_symm (superpose eq11 eq11)
  have eq32 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq25 eq17 | exact mod_symm (superpose eq25 eq17) | exact superpose eq17 eq25 | exact mod_symm (superpose eq17 eq25)
  have eq35 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ (e (e (v X0)))) := by first | exact superpose eq13 eq16 | exact mod_symm (superpose eq13 eq16) | exact superpose eq16 eq13 | exact mod_symm (superpose eq16 eq13)
  have eq41 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ (e (v X0))) := by first | exact superpose eq12 eq35 | exact mod_symm (superpose eq12 eq35) | exact superpose eq35 eq12 | exact mod_symm (superpose eq35 eq12)
  have eq45 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq16 eq41 | exact mod_symm (superpose eq16 eq41) | exact superpose eq41 eq16 | exact mod_symm (superpose eq41 eq16)
  have eq48 : (w x y) ≠ (w y x) := by first | exact superpose eq45 eq32 | exact mod_symm (superpose eq45 eq32) | exact superpose eq32 eq45 | exact mod_symm (superpose eq32 eq45)
  have eq163 (X0 X1 : G) : ((e X0) ◇ X1) = (X1 ◇ ((v X0) ◇ (v X0))) := by first | exact superpose eq26 eq28 | exact mod_symm (superpose eq26 eq28) | exact superpose eq28 eq26 | exact mod_symm (superpose eq28 eq26)
  have eq175 (X0 X1 : G) : ((e X0) ◇ X1) = (X1 ◇ (e X0)) := by first | exact superpose eq14 eq163 | exact mod_symm (superpose eq14 eq163) | exact superpose eq163 eq14 | exact mod_symm (superpose eq163 eq14)
  have eq205 (X0 X1 : G) : ((e (v X0)) ◇ (e (v X1))) = (w X1 X0) := by first | exact superpose eq175 eq16 | exact mod_symm (superpose eq175 eq16) | exact superpose eq16 eq175 | exact mod_symm (superpose eq16 eq175)
  have eq2478 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq205 eq16 | exact mod_symm (superpose eq205 eq16) | exact superpose eq16 eq205 | exact mod_symm (superpose eq16 eq205)
  have eq2771 : (w x y) ≠ (w x y) := by first | exact superpose eq2478 eq48 | exact mod_symm (superpose eq2478 eq48) | exact superpose eq48 eq2478 | exact mod_symm (superpose eq48 eq2478)
  first | exact eq2771 rfl | exact eq2771 _ rfl | exact eq2771 _ _ rfl | exact eq2771 _ _ _ rfl


theorem Equation332_termDefinableFromFin_Equation3364 :
    Law332.TermDefinableFromFin Law3364 := by
  refine termDefinableFromFin_of_iterate_pair (fun G ↦ (tm1 (Term.var 0) (Term.var 0)))
    (fun G ↦ (tm (Term.var 0) (Term.var 1))) 0 0 true true 1 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation3364 G := Law3364.models_iff.mp hGL
  have huv : ∀ a : G, ((v a) ◇ (v a)) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ a) = e a := fun a ↦ he.v_comp_u a
  rw [@Law332.models_iff]
  intro x y
  exact aux3364_332 h e v _ he.idem he.comm_v huv hvu (fun a b ↦ rfl) x y

end Law.MagmaLaw
