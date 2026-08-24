import equational_theories.Definability.OuterIterate
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Source 492: cells landed by an idempotent iterate applied outside the defining term

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

/-- On a finite carrier a one-sided inverse is two-sided: this is what turns a source law into its
cyclic rotations. Applied with `f` the outer part of the chain and `g` its first factor, it moves
`g` from the inside of the composite to the outside. -/
private theorem rot_of_finite [Finite G] {f g : G → G} (hfg : ∀ z, f (g z) = z) (x : G) :
    g (f x) = x := by
  have hs : Function.Surjective f := fun z ↦ ⟨g z, hfg z⟩
  exact Finite.injective_iff_surjective.mpr hs (hfg (f x))


/-- Equation 332 `x ◇ y = y ◇ (x ◇ x)` is term-definable from equation 492 over finite magmas, via the term
`x □ y := (x ◇ y)` with `u a = (a ◇ a)`
taken at x at u^[2N+1], y at u^[2N+1]. -/
private theorem aux492_332 [Finite G] [Magma G] (h : Equation492 G)
    (e v : G → G) (w : G → G → G)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huv : ∀ a : G, ((v a) ◇ (v a)) = e a)
    (hvu : ∀ a : G, v (a ◇ a) = e a)
    (hw : ∀ a b : G, w a b = ((e (v a)) ◇ (e (v b))))
    (x y : G) :
    (w x y) =
      (w y (w x x)) := by
  have hrot0 (a b c : G) : (b ◇ a) ◇ (c ◇ (c ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (c ◇ (c ◇ b)))
      (fun z ↦ (h z b c).symm) a
  by_contra nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (hrot0 ..)
  have eq14 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq15 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq16 (X0 : G) : (e X0) = ((v X0) ◇ (v X0)) := mod_symm (huv ..)
  have eq18 (X0 X1 : G) : (w X0 X1) = ((e (v X0)) ◇ (e (v X1))) := mod_symm (hw ..)
  have eq19 : (w x y) ≠ (w y (w x x)) := mod_symm nh
  have eq23 (X0 : G) : (e (e X0)) = ((e (v X0)) ◇ (e (v X0))) := by first | exact superpose eq15 eq16 | exact mod_symm (superpose eq15 eq16) | exact superpose eq16 eq15 | exact mod_symm (superpose eq16 eq15)
  have eq26 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq18 eq23 | exact mod_symm (superpose eq18 eq23) | exact superpose eq23 eq18 | exact mod_symm (superpose eq23 eq18)
  have eq27 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq29 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X2 ◇ X0))) = X3 := by first | exact superpose eq12 eq12 | exact mod_symm (superpose eq12 eq12) | exact superpose eq12 eq12 | exact mod_symm (superpose eq12 eq12)
  have eq31 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := by first | exact superpose eq12 eq12 | exact mod_symm (superpose eq12 eq12) | exact superpose eq12 eq12 | exact mod_symm (superpose eq12 eq12)
  have eq32 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq27 eq19 | exact mod_symm (superpose eq27 eq19) | exact superpose eq19 eq27 | exact mod_symm (superpose eq19 eq27)
  have eq41 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X2 := by first | exact superpose eq13 eq12 | exact mod_symm (superpose eq13 eq12) | exact superpose eq12 eq13 | exact mod_symm (superpose eq12 eq13)
  have eq45 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := by first | exact superpose eq31 eq41 | exact mod_symm (superpose eq31 eq41) | exact superpose eq41 eq31 | exact mod_symm (superpose eq41 eq31)
  have eq49 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ (e (e (v X0)))) := by first | exact superpose eq15 eq18 | exact mod_symm (superpose eq15 eq18) | exact superpose eq18 eq15 | exact mod_symm (superpose eq18 eq15)
  have eq57 (X0 X1 : G) : (w X1 (e X0)) = ((e (v X1)) ◇ (e (v X0))) := by first | exact superpose eq14 eq49 | exact mod_symm (superpose eq14 eq49) | exact superpose eq49 eq14 | exact mod_symm (superpose eq49 eq14)
  have eq61 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq18 eq57 | exact mod_symm (superpose eq18 eq57) | exact superpose eq57 eq18 | exact mod_symm (superpose eq57 eq18)
  have eq63 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X1))) = (X0 ◇ X1) := by first | exact superpose eq12 eq31 | exact mod_symm (superpose eq12 eq31) | exact superpose eq31 eq12 | exact mod_symm (superpose eq31 eq12)
  have eq64 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by first | exact superpose eq13 eq31 | exact mod_symm (superpose eq13 eq31) | exact superpose eq31 eq13 | exact mod_symm (superpose eq31 eq13)
  have eq72 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = X1 := by first | exact superpose eq45 eq64 | exact mod_symm (superpose eq45 eq64) | exact superpose eq64 eq45 | exact mod_symm (superpose eq64 eq45)
  have eq112 : (w x y) ≠ (w y x) := by first | exact superpose eq61 eq32 | exact mod_symm (superpose eq61 eq32) | exact superpose eq32 eq61 | exact mod_symm (superpose eq32 eq61)
  have eq1256 (X0 X1 X2 X3 : G) : (((e (v X1)) ◇ (X2 ◇ (X2 ◇ (e (v X0))))) ◇ (X3 ◇ (w X0 X1))) = X3 := by first | exact superpose eq18 eq29 | exact mod_symm (superpose eq18 eq29) | exact superpose eq29 eq18 | exact mod_symm (superpose eq29 eq18)
  have eq1365 (X0 X1 X3 : G) : (((e (v X1)) ◇ (e (v X0))) ◇ (X3 ◇ (w X0 X1))) = X3 := by first | exact superpose eq63 eq1256 | exact mod_symm (superpose eq63 eq1256) | exact superpose eq1256 eq63 | exact mod_symm (superpose eq1256 eq63)
  have eq1437 (X0 X1 X3 : G) : ((w X1 X0) ◇ (X3 ◇ (w X0 X1))) = X3 := by first | exact superpose eq18 eq1365 | exact mod_symm (superpose eq18 eq1365) | exact superpose eq1365 eq18 | exact mod_symm (superpose eq1365 eq18)
  have eq8197 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq1437 eq72 | exact mod_symm (superpose eq1437 eq72) | exact superpose eq72 eq1437 | exact mod_symm (superpose eq72 eq1437)
  have eq8369 : (w x y) ≠ (w x y) := by first | exact superpose eq8197 eq112 | exact mod_symm (superpose eq8197 eq112) | exact superpose eq112 eq8197 | exact mod_symm (superpose eq112 eq8197)
  first | exact eq8369 rfl | exact eq8369 _ rfl | exact eq8369 _ _ rfl | exact eq8369 _ _ _ rfl


theorem Equation332_termDefinableFromFin_Equation492 :
    Law332.TermDefinableFromFin Law492 := by
  refine termDefinableFromFin_of_iterate_pair (fun G ↦ (tm1 (Term.var 0) (Term.var 0)))
    (fun G ↦ (tm (Term.var 0) (Term.var 1))) 0 0 true true 1 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation492 G := Law492.models_iff.mp hGL
  have huv : ∀ a : G, ((v a) ◇ (v a)) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ a) = e a := fun a ↦ he.v_comp_u a
  rw [@Law332.models_iff]
  intro x y
  exact aux492_332 h e v _ he.idem he.comm_v huv hvu (fun a b ↦ rfl) x y

end Law.MagmaLaw
