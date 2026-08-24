import equational_theories.Definability.OuterIterate
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Source 4343: cells landed by an idempotent iterate applied outside the defining term

The unary term (x(xx)) is iterated outside the defining term. `OuterIterate.lean` names the two
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


/-- Equation 332 `x ◇ y = y ◇ (x ◇ x)` is term-definable from equation 4343 over finite magmas, via the term
`x □ y := (x ◇ (y ◇ y))` with `u a = (a ◇ (a ◇ a))`
taken at x at u^[2N+1], y at u^[2N+1]. -/
private theorem aux4343_332 [Magma G] (h : Equation4343 G) (e v : G → G) (w : G → G → G)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a)
    (hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a)
    (hw : ∀ a b : G, w a b = ((e (v a)) ◇ ((e (v b)) ◇ (e (v b)))))
    (x y : G) :
    (w x y) =
      (w y (w x x)) := by
  by_contra nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq12 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq13 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq14 (X0 : G) : (e X0) = ((v X0) ◇ ((v X0) ◇ (v X0))) := mod_symm (huv ..)
  have eq16 (X0 X1 : G) : (w X0 X1) = ((e (v X0)) ◇ ((e (v X1)) ◇ (e (v X1)))) := mod_symm (hw ..)
  have eq17 : (w x y) ≠ (w y (w x x)) := mod_symm nh
  have eq21 (X0 : G) : (e (e X0)) = ((e (v X0)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14) | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13)
  have eq24 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq16 eq21 | exact mod_symm (superpose eq16 eq21) | exact superpose eq21 eq16 | exact mod_symm (superpose eq21 eq16)
  have eq25 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq12 eq24 | exact mod_symm (superpose eq12 eq24) | exact superpose eq24 eq12 | exact mod_symm (superpose eq24 eq12)
  have eq26 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq25 eq17 | exact mod_symm (superpose eq25 eq17) | exact superpose eq17 eq25 | exact mod_symm (superpose eq17 eq25)
  have eq29 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ ((e (e (v X0))) ◇ (e (e (v X0))))) := by first | exact superpose eq13 eq16 | exact mod_symm (superpose eq13 eq16) | exact superpose eq16 eq13 | exact mod_symm (superpose eq16 eq13)
  have eq35 (X0 X1 : G) : (w X0 X1) = ((e (v X1)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq16 eq11 | exact mod_symm (superpose eq16 eq11) | exact superpose eq11 eq16 | exact mod_symm (superpose eq11 eq16)
  have eq38 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq12 eq29 | exact mod_symm (superpose eq12 eq29) | exact superpose eq29 eq12 | exact mod_symm (superpose eq29 eq12)
  have eq42 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq16 eq38 | exact mod_symm (superpose eq16 eq38) | exact superpose eq38 eq16 | exact mod_symm (superpose eq38 eq16)
  have eq45 : (w x y) ≠ (w y x) := by first | exact superpose eq42 eq26 | exact mod_symm (superpose eq42 eq26) | exact superpose eq26 eq42 | exact mod_symm (superpose eq26 eq42)
  have eq79 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq35 eq16 | exact mod_symm (superpose eq35 eq16) | exact superpose eq16 eq35 | exact mod_symm (superpose eq16 eq35)
  have eq105 : (w x y) ≠ (w x y) := by first | exact superpose eq79 eq45 | exact mod_symm (superpose eq79 eq45) | exact superpose eq45 eq79 | exact mod_symm (superpose eq45 eq79)
  first | exact eq105 rfl | exact eq105 _ rfl | exact eq105 _ _ rfl | exact eq105 _ _ _ rfl


/-- Equation 3342 `x ◇ y = y ◇ (x ◇ (x ◇ x))` is term-definable from equation 4343 over finite magmas, via the term
`x □ y := (x ◇ (y ◇ y))` with `u a = (a ◇ (a ◇ a))`
taken at x at u^[2N+1], y at u^[2N+1]. -/
private theorem aux4343_3342 [Magma G] (h : Equation4343 G) (e v : G → G) (w : G → G → G)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a)
    (hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a)
    (hw : ∀ a b : G, w a b = ((e (v a)) ◇ ((e (v b)) ◇ (e (v b)))))
    (x y : G) :
    (w x y) =
      (w y (w x (w x x))) := by
  by_contra nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq12 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq13 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq14 (X0 : G) : (e X0) = ((v X0) ◇ ((v X0) ◇ (v X0))) := mod_symm (huv ..)
  have eq16 (X0 X1 : G) : (w X0 X1) = ((e (v X0)) ◇ ((e (v X1)) ◇ (e (v X1)))) := mod_symm (hw ..)
  have eq17 : (w x y) ≠ (w y (w x (w x x))) := mod_symm nh
  have eq21 (X0 : G) : (e (e X0)) = ((e (v X0)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14) | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13)
  have eq24 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq16 eq21 | exact mod_symm (superpose eq16 eq21) | exact superpose eq21 eq16 | exact mod_symm (superpose eq21 eq16)
  have eq25 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq12 eq24 | exact mod_symm (superpose eq12 eq24) | exact superpose eq24 eq12 | exact mod_symm (superpose eq24 eq12)
  have eq26 : (w x y) ≠ (w y (w x (e x))) := by first | exact superpose eq25 eq17 | exact mod_symm (superpose eq25 eq17) | exact superpose eq17 eq25 | exact mod_symm (superpose eq17 eq25)
  have eq29 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ ((e (e (v X0))) ◇ (e (e (v X0))))) := by first | exact superpose eq13 eq16 | exact mod_symm (superpose eq13 eq16) | exact superpose eq16 eq13 | exact mod_symm (superpose eq16 eq13)
  have eq35 (X0 X1 : G) : (w X0 X1) = ((e (v X1)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq16 eq11 | exact mod_symm (superpose eq16 eq11) | exact superpose eq11 eq16 | exact mod_symm (superpose eq11 eq16)
  have eq38 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq12 eq29 | exact mod_symm (superpose eq12 eq29) | exact superpose eq29 eq12 | exact mod_symm (superpose eq29 eq12)
  have eq42 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq16 eq38 | exact mod_symm (superpose eq16 eq38) | exact superpose eq38 eq16 | exact mod_symm (superpose eq38 eq16)
  have eq45 : (w x y) ≠ (w y (w x x)) := by first | exact superpose eq42 eq26 | exact mod_symm (superpose eq42 eq26) | exact superpose eq26 eq42 | exact mod_symm (superpose eq26 eq42)
  have eq48 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq25 eq45 | exact mod_symm (superpose eq25 eq45) | exact superpose eq45 eq25 | exact mod_symm (superpose eq45 eq25)
  have eq51 : (w x y) ≠ (w y x) := by first | exact superpose eq42 eq48 | exact mod_symm (superpose eq42 eq48) | exact superpose eq48 eq42 | exact mod_symm (superpose eq48 eq42)
  have eq81 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq35 eq16 | exact mod_symm (superpose eq35 eq16) | exact superpose eq16 eq35 | exact mod_symm (superpose eq16 eq35)
  have eq107 : (w x y) ≠ (w x y) := by first | exact superpose eq81 eq51 | exact mod_symm (superpose eq81 eq51) | exact superpose eq51 eq81 | exact mod_symm (superpose eq51 eq81)
  first | exact eq107 rfl | exact eq107 _ rfl | exact eq107 _ _ rfl | exact eq107 _ _ _ rfl


/-- Equation 3545 `x ◇ y = y ◇ ((x ◇ x) ◇ x)` is term-definable from equation 4343 over finite magmas, via the term
`x □ y := (x ◇ (y ◇ y))` with `u a = (a ◇ (a ◇ a))`
taken at x at u^[2N+1], y at u^[2N+1]. -/
private theorem aux4343_3545 [Magma G] (h : Equation4343 G) (e v : G → G) (w : G → G → G)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a)
    (hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a)
    (hw : ∀ a b : G, w a b = ((e (v a)) ◇ ((e (v b)) ◇ (e (v b)))))
    (x y : G) :
    (w x y) =
      (w y (w (w x x) x)) := by
  by_contra nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have eq12 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq13 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq14 (X0 : G) : (e X0) = ((v X0) ◇ ((v X0) ◇ (v X0))) := mod_symm (huv ..)
  have eq16 (X0 X1 : G) : (w X0 X1) = ((e (v X0)) ◇ ((e (v X1)) ◇ (e (v X1)))) := mod_symm (hw ..)
  have eq17 : (w x y) ≠ (w y (w (w x x) x)) := mod_symm nh
  have eq21 (X0 : G) : (e (e X0)) = ((e (v X0)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14) | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13)
  have eq24 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq16 eq21 | exact mod_symm (superpose eq16 eq21) | exact superpose eq21 eq16 | exact mod_symm (superpose eq21 eq16)
  have eq25 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq12 eq24 | exact mod_symm (superpose eq12 eq24) | exact superpose eq24 eq12 | exact mod_symm (superpose eq24 eq12)
  have eq26 : (w x y) ≠ (w y (w (e x) x)) := by first | exact superpose eq25 eq17 | exact mod_symm (superpose eq25 eq17) | exact superpose eq17 eq25 | exact mod_symm (superpose eq17 eq25)
  have eq27 (X0 X1 : G) : (w (e X0) X1) = ((e (e (v X0))) ◇ ((e (v X1)) ◇ (e (v X1)))) := by first | exact superpose eq13 eq16 | exact mod_symm (superpose eq13 eq16) | exact superpose eq16 eq13 | exact mod_symm (superpose eq16 eq13)
  have eq29 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ ((e (e (v X0))) ◇ (e (e (v X0))))) := by first | exact superpose eq13 eq16 | exact mod_symm (superpose eq13 eq16) | exact superpose eq16 eq13 | exact mod_symm (superpose eq16 eq13)
  have eq35 (X0 X1 : G) : (w X0 X1) = ((e (v X1)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq16 eq11 | exact mod_symm (superpose eq16 eq11) | exact superpose eq11 eq16 | exact mod_symm (superpose eq11 eq16)
  have eq38 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ ((e (v X0)) ◇ (e (v X0)))) := by first | exact superpose eq12 eq29 | exact mod_symm (superpose eq12 eq29) | exact superpose eq29 eq12 | exact mod_symm (superpose eq29 eq12)
  have eq40 (X0 X1 : G) : ((e (v X0)) ◇ ((e (v X1)) ◇ (e (v X1)))) = (w (e X0) X1) := by first | exact superpose eq12 eq27 | exact mod_symm (superpose eq12 eq27) | exact superpose eq27 eq12 | exact mod_symm (superpose eq27 eq12)
  have eq42 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq16 eq38 | exact mod_symm (superpose eq16 eq38) | exact superpose eq38 eq16 | exact mod_symm (superpose eq38 eq16)
  have eq43 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq16 eq40 | exact mod_symm (superpose eq16 eq40) | exact superpose eq40 eq16 | exact mod_symm (superpose eq40 eq16)
  have eq54 : (w x y) ≠ (w y (w x x)) := by first | exact superpose eq43 eq26 | exact mod_symm (superpose eq43 eq26) | exact superpose eq26 eq43 | exact mod_symm (superpose eq26 eq43)
  have eq55 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq25 eq54 | exact mod_symm (superpose eq25 eq54) | exact superpose eq54 eq25 | exact mod_symm (superpose eq54 eq25)
  have eq60 : (w x y) ≠ (w y x) := by first | exact superpose eq42 eq55 | exact mod_symm (superpose eq42 eq55) | exact superpose eq55 eq42 | exact mod_symm (superpose eq55 eq42)
  have eq81 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq35 eq16 | exact mod_symm (superpose eq35 eq16) | exact superpose eq16 eq35 | exact mod_symm (superpose eq16 eq35)
  have eq111 : (w x y) ≠ (w x y) := by first | exact superpose eq81 eq60 | exact mod_symm (superpose eq81 eq60) | exact superpose eq60 eq81 | exact mod_symm (superpose eq60 eq81)
  first | exact eq111 rfl | exact eq111 _ rfl | exact eq111 _ _ rfl | exact eq111 _ _ _ rfl


theorem Equation332_termDefinableFromFin_Equation4343 :
    Law332.TermDefinableFromFin Law4343 := by
  refine termDefinableFromFin_of_iterate_pair (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))))
    (fun G ↦ (tm (Term.var 0) (tm (Term.var 1) (Term.var 1)))) 0 0 true true 1 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4343 G := Law4343.models_iff.mp hGL
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a := fun a ↦ he.v_comp_u a
  rw [@Law332.models_iff]
  intro x y
  exact aux4343_332 h e v _ he.idem he.comm_v huv hvu (fun a b ↦ rfl) x y

theorem Equation3342_termDefinableFromFin_Equation4343 :
    Law3342.TermDefinableFromFin Law4343 := by
  refine termDefinableFromFin_of_iterate_pair (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))))
    (fun G ↦ (tm (Term.var 0) (tm (Term.var 1) (Term.var 1)))) 0 0 true true 1 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4343 G := Law4343.models_iff.mp hGL
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a := fun a ↦ he.v_comp_u a
  rw [@Law3342.models_iff]
  intro x y
  exact aux4343_3342 h e v _ he.idem he.comm_v huv hvu (fun a b ↦ rfl) x y

theorem Equation3545_termDefinableFromFin_Equation4343 :
    Law3545.TermDefinableFromFin Law4343 := by
  refine termDefinableFromFin_of_iterate_pair (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))))
    (fun G ↦ (tm (Term.var 0) (tm (Term.var 1) (Term.var 1)))) 0 0 true true 1 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4343 G := Law4343.models_iff.mp hGL
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a := fun a ↦ he.v_comp_u a
  rw [@Law3545.models_iff]
  intro x y
  exact aux4343_3545 h e v _ he.idem he.comm_v huv hvu (fun a b ↦ rfl) x y

end Law.MagmaLaw
