import equational_theories.Definability.OuterIterate
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Source 4364: cells landed by an idempotent iterate applied outside the defining term

Equation 4364 `x ◇ (y ◇ z) = y ◇ (z ◇ x)` makes the unary term (x(xx)), (x(x(xx))) a magma endomorphism, so every iterate of it
distributes over `◇` and a defining term may be wrapped in one. `OuterIterate.lean` names the two
families of iterates the device can reach -- `v^[k] = u^[N k]` and `e ∘ v^[k] = u^[N k + N + 1]` --
and each cell below picks the wrapper and the base term that its target needs.

The endomorphism fact is proved from equation 4364 alone; the exponent is chosen after the magma,
which is why these are finite-flavour statements.
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


/-- `u a = (a ◇ (a ◇ a))` is a magma endomorphism, from equation 4364 alone. -/
private theorem endo4364_0 [Magma G] (h : Equation4364 G) (x y : G) :
    ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) = (x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y)) := by
  by_contra nh
  have eq6 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have eq7 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ ((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) := mod_symm nh
  have eq8 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq15 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ ((y ◇ y) ◇ ((x ◇ (x ◇ x)) ◇ y)) := by first | exact superpose eq6 eq7 | exact mod_symm (superpose eq6 eq7) | exact superpose eq7 eq6 | exact mod_symm (superpose eq7 eq6)
  have eq16 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ (y ◇ ((y ◇ y) ◇ (x ◇ (x ◇ x)))) := by first | exact superpose eq6 eq15 | exact mod_symm (superpose eq6 eq15) | exact superpose eq15 eq6 | exact mod_symm (superpose eq15 eq6)
  have eq18 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ (x ◇ (((x ◇ x) ◇ (y ◇ y)) ◇ y)) := by first | exact superpose eq8 eq16 | exact mod_symm (superpose eq8 eq16) | exact superpose eq16 eq8 | exact mod_symm (superpose eq16 eq8)
  have eq20 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ (x ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ y)) := by first | exact superpose eq6 eq18 | exact mod_symm (superpose eq6 eq18) | exact superpose eq18 eq6 | exact mod_symm (superpose eq18 eq6)
  have eq22 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ (x ◇ ((x ◇ ((y ◇ x) ◇ y)) ◇ y)) := by first | exact superpose eq9 eq20 | exact mod_symm (superpose eq9 eq20) | exact superpose eq20 eq9 | exact mod_symm (superpose eq20 eq9)
  have eq24 : (x ◇ ((x ◇ ((y ◇ x) ◇ y)) ◇ y)) ≠ (y ◇ (((x ◇ y) ◇ x) ◇ (x ◇ y))) := by first | exact superpose eq9 eq22 | exact mod_symm (superpose eq9 eq22) | exact superpose eq22 eq9 | exact mod_symm (superpose eq22 eq9)
  have eq26 : (x ◇ ((x ◇ ((y ◇ x) ◇ y)) ◇ y)) ≠ (x ◇ ((y ◇ ((x ◇ y) ◇ x)) ◇ y)) := by first | exact superpose eq8 eq24 | exact mod_symm (superpose eq8 eq24) | exact superpose eq24 eq8 | exact mod_symm (superpose eq24 eq8)
  have eq28 : (x ◇ ((x ◇ ((y ◇ x) ◇ y)) ◇ y)) ≠ (x ◇ ((x ◇ (y ◇ (x ◇ y))) ◇ y)) := by first | exact superpose eq6 eq26 | exact mod_symm (superpose eq6 eq26) | exact superpose eq26 eq6 | exact mod_symm (superpose eq26 eq6)
  have eq30 : (x ◇ ((x ◇ ((y ◇ x) ◇ y)) ◇ y)) ≠ (x ◇ ((x ◇ (x ◇ (y ◇ y))) ◇ y)) := by first | exact superpose eq6 eq28 | exact mod_symm (superpose eq6 eq28) | exact superpose eq28 eq6 | exact mod_symm (superpose eq28 eq6)
  have eq58 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by first | exact superpose eq8 eq6 | exact mod_symm (superpose eq8 eq6) | exact superpose eq6 eq8 | exact mod_symm (superpose eq6 eq8)
  have eq59 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by first | exact superpose eq8 eq6 | exact mod_symm (superpose eq8 eq6) | exact superpose eq6 eq8 | exact mod_symm (superpose eq6 eq8)
  have eq978 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X4 ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) := by first | exact superpose eq9 eq58 | exact mod_symm (superpose eq9 eq58) | exact superpose eq58 eq9 | exact mod_symm (superpose eq58 eq9)
  have eq1068 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0)) = (X4 ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) := by first | exact superpose eq58 eq978 | exact mod_symm (superpose eq58 eq978) | exact superpose eq978 eq58 | exact mod_symm (superpose eq978 eq58)
  have eq1297 : (x ◇ ((x ◇ (x ◇ (y ◇ y))) ◇ y)) ≠ (x ◇ ((x ◇ ((x ◇ y) ◇ y)) ◇ y)) := by first | exact superpose eq59 eq30 | exact mod_symm (superpose eq59 eq30) | exact superpose eq30 eq59 | exact mod_symm (superpose eq30 eq59)
  subsumption eq1297 eq1068


/-- `u a = (a ◇ (a ◇ (a ◇ a)))` is a magma endomorphism, from equation 4364 alone. -/
private theorem endo4364_1 [Magma G] (h : Equation4364 G) (x y : G) :
    ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) = (x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (y ◇ (y ◇ y))) := by
  by_contra nh
  have eq6 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have eq7 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (y ◇ (y ◇ y)))) := mod_symm nh
  have eq8 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X5 ◇ X3))) = (X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) := by first | exact superpose eq8 eq8 | exact mod_symm (superpose eq8 eq8) | exact superpose eq8 eq8 | exact mod_symm (superpose eq8 eq8)
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = ((X3 ◇ X1) ◇ ((X0 ◇ X2) ◇ X4)) := by first | exact superpose eq8 eq8 | exact mod_symm (superpose eq8 eq8) | exact superpose eq8 eq8 | exact mod_symm (superpose eq8 eq8)
  have eq61 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = (X0 ◇ ((X1 ◇ (X4 ◇ X2)) ◇ X3)) := by first | exact superpose eq8 eq8 | exact mod_symm (superpose eq8 eq8) | exact superpose eq8 eq8 | exact mod_symm (superpose eq8 eq8)
  have eq62 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X3 ◇ X1))) := by first | exact superpose eq8 eq6 | exact mod_symm (superpose eq8 eq6) | exact superpose eq6 eq8 | exact mod_symm (superpose eq6 eq8)
  have eq65 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X2 ◇ (((X3 ◇ X1) ◇ X0) ◇ X4)) := by first | exact superpose eq8 eq6 | exact mod_symm (superpose eq8 eq6) | exact superpose eq6 eq8 | exact mod_symm (superpose eq6 eq8)
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by first | exact superpose eq8 eq6 | exact mod_symm (superpose eq8 eq6) | exact superpose eq6 eq8 | exact mod_symm (superpose eq6 eq8)
  have eq73 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X4 ◇ X2)) ◇ X3)) = (X0 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X2)) := by first | exact superpose eq66 eq61 | exact mod_symm (superpose eq66 eq61) | exact superpose eq61 eq66 | exact mod_symm (superpose eq61 eq66)
  have eq74 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X3 ◇ ((X1 ◇ X4) ◇ (X0 ◇ X2))) := by first | exact superpose eq66 eq58 | exact mod_symm (superpose eq66 eq58) | exact superpose eq58 eq66 | exact mod_symm (superpose eq58 eq66)
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X5 ◇ X3))) = (X5 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X4) ◇ X3)))) := by first | exact superpose eq66 eq46 | exact mod_symm (superpose eq66 eq46) | exact superpose eq46 eq66 | exact mod_symm (superpose eq46 eq66)
  have eq86 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X3 ◇ (X1 ◇ ((X4 ◇ X2) ◇ X0))) := by first | exact superpose eq66 eq74 | exact mod_symm (superpose eq66 eq74) | exact superpose eq74 eq66 | exact mod_symm (superpose eq74 eq66)
  have eq88 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X4) ◇ X3)))) = (X2 ◇ (((X0 ◇ X1) ◇ (X5 ◇ X3)) ◇ X4)) := by first | exact superpose eq66 eq77 | exact mod_symm (superpose eq66 eq77) | exact superpose eq77 eq66 | exact mod_symm (superpose eq77 eq66)
  have eq93 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X4) ◇ X3)))) = (X2 ◇ ((X0 ◇ ((X1 ◇ X3) ◇ X5)) ◇ X4)) := by first | exact superpose eq66 eq88 | exact mod_symm (superpose eq66 eq88) | exact superpose eq88 eq66 | exact mod_symm (superpose eq88 eq66)
  have eq151 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ ((y ◇ y) ◇ ((y ◇ y) ◇ (x ◇ (x ◇ (x ◇ x))))) := by first | exact superpose eq9 eq7 | exact mod_symm (superpose eq9 eq7) | exact superpose eq7 eq9 | exact mod_symm (superpose eq7 eq9)
  have eq169 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (((x ◇ (x ◇ x)) ◇ (y ◇ y)) ◇ (y ◇ y))) := by first | exact superpose eq8 eq151 | exact mod_symm (superpose eq8 eq151) | exact superpose eq151 eq8 | exact mod_symm (superpose eq151 eq8)
  have eq196 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (y ◇ (y ◇ ((x ◇ (x ◇ x)) ◇ (y ◇ y))))) := by first | exact superpose eq62 eq169 | exact mod_symm (superpose eq62 eq169) | exact superpose eq169 eq62 | exact mod_symm (superpose eq169 eq62)
  have eq213 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ ((y ◇ y) ◇ (y ◇ ((x ◇ x) ◇ y))))) := by first | exact superpose eq86 eq196 | exact mod_symm (superpose eq86 eq196) | exact superpose eq196 eq86 | exact mod_symm (superpose eq196 eq86)
  have eq222 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (y ◇ (((x ◇ x) ◇ y) ◇ (y ◇ y))))) := by first | exact superpose eq62 eq213 | exact mod_symm (superpose eq62 eq213) | exact superpose eq213 eq62 | exact mod_symm (superpose eq213 eq62)
  have eq225 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ ((x ◇ x) ◇ y)))))) := by first | exact superpose eq62 eq222 | exact mod_symm (superpose eq62 eq222) | exact superpose eq222 eq62 | exact mod_symm (superpose eq222 eq62)
  have eq226 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)))) := by first | exact superpose eq93 eq225 | exact mod_symm (superpose eq93 eq225) | exact superpose eq225 eq93 | exact mod_symm (superpose eq225 eq93)
  have eq227 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y)))))) := by first | exact superpose eq62 eq226 | exact mod_symm (superpose eq62 eq226) | exact superpose eq226 eq62 | exact mod_symm (superpose eq226 eq62)
  have eq228 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq62 eq227 | exact mod_symm (superpose eq62 eq227) | exact superpose eq227 eq62 | exact mod_symm (superpose eq227 eq62)
  have eq229 : (x ◇ (((y ◇ (x ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ y))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq65 eq228 | exact mod_symm (superpose eq65 eq228) | exact superpose eq228 eq65 | exact mod_symm (superpose eq228 eq65)
  have eq230 : (x ◇ (x ◇ (y ◇ ((y ◇ (x ◇ y)) ◇ (x ◇ y))))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq62 eq229 | exact mod_symm (superpose eq62 eq229) | exact superpose eq229 eq62 | exact mod_symm (superpose eq229 eq62)
  have eq231 : (x ◇ (x ◇ (x ◇ ((y ◇ (y ◇ (x ◇ y))) ◇ y)))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq8 eq230 | exact mod_symm (superpose eq8 eq230) | exact superpose eq230 eq8 | exact mod_symm (superpose eq230 eq8)
  have eq232 : (x ◇ (x ◇ (x ◇ ((y ◇ (y ◇ y)) ◇ (x ◇ y))))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq73 eq231 | exact mod_symm (superpose eq73 eq231) | exact superpose eq231 eq73 | exact mod_symm (superpose eq231 eq73)
  have eq233 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq62 eq232 | exact mod_symm (superpose eq62 eq232) | exact superpose eq232 eq62 | exact mod_symm (superpose eq232 eq62)
  first | exact eq233 rfl | exact eq233 _ rfl | exact eq233 _ _ rfl | exact eq233 _ _ _ rfl


/-- Equation 332 `x ◇ y = y ◇ (x ◇ x)` is term-definable from equation 4364 over finite magmas, via the term
`x □ y := u^[2N+1] (((x ◇ x) ◇ y) ◇ y)` with `u a = (a ◇ (a ◇ (a ◇ a)))`. -/
private theorem aux4364_332 [Magma G] (h : Equation4364 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, ((v (e a)) ◇ ((v (e a)) ◇ ((v (e a)) ◇ (v (e a))))) = e a)
    (hvue : ∀ a : G, v ((e a) ◇ ((e a) ◇ ((e a) ◇ (e a)))) = e a)
    (hw : ∀ a b : G, w a b = (e (v ((((a ◇ a) ◇ b) ◇ b)))))
    (x y : G) :
    (w x y) =
      (w y (w x x)) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ ((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0))))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ ((e X0) ◇ ((e X0) ◇ (e X0))))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) := mod_symm (hw ..)
  have eq21 : (w x y) ≠ (w y (w x x)) := mod_symm nh
  have eq25 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq26 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq28 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq25 | exact mod_symm (superpose eq14 eq25) | exact superpose eq25 eq14 | exact mod_symm (superpose eq25 eq14)
  have eq29 (X0 X1 : G) : (v ((e X0) ◇ X1)) = ((e (v X0)) ◇ (v X1)) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq30 (X0 X1 : G) : (v (X1 ◇ (e X0))) = ((v X1) ◇ (e (v X0))) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq31 (X0 X1 X2 : G) : ((e X0) ◇ ((e X1) ◇ X2)) = (X2 ◇ (e (X0 ◇ X1))) := by first | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13) | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14)
  have eq32 (X0 X1 X2 : G) : ((v X0) ◇ ((v X1) ◇ X2)) = (X2 ◇ (v (X0 ◇ X1))) := by first | exact superpose eq15 eq13 | exact mod_symm (superpose eq15 eq13) | exact superpose eq13 eq15 | exact mod_symm (superpose eq13 eq15)
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq34 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq36 (X0 X1 X2 : G) : (X2 ◇ (e (X0 ◇ X1))) = ((e X1) ◇ (X2 ◇ (e X0))) := by first | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13) | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14)
  have eq37 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ (X2 ◇ (v X0))) := by first | exact superpose eq15 eq13 | exact mod_symm (superpose eq15 eq13) | exact superpose eq13 eq15 | exact mod_symm (superpose eq13 eq15)
  have eq39 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq44 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = ((e (X0 ◇ X1)) ◇ (e X2)) := by first | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14) | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27)
  have eq45 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq27 eq17 | exact mod_symm (superpose eq27 eq17) | exact superpose eq17 eq27 | exact mod_symm (superpose eq17 eq27)
  have eq47 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq45 | exact mod_symm (superpose eq17 eq45) | exact superpose eq45 eq17 | exact mod_symm (superpose eq45 eq17)
  have eq48 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = (e ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq14 eq44 | exact mod_symm (superpose eq14 eq44) | exact superpose eq44 eq14 | exact mod_symm (superpose eq44 eq14)
  have eq52 (X0 X1 : G) : (w (e X0) X1) = (e (v (((e (X0 ◇ X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq75 (X0 : G) : (e X0) = (v ((e X0) ◇ ((e X0) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq80 (X0 : G) : (e X0) = (v ((e X0) ◇ (e ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq36 eq75 | exact mod_symm (superpose eq36 eq75) | exact superpose eq75 eq36 | exact mod_symm (superpose eq75 eq36)
  have eq83 (X0 : G) : (e X0) = (v (e (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq14 eq80 | exact mod_symm (superpose eq14 eq80) | exact superpose eq80 eq14 | exact mod_symm (superpose eq80 eq14)
  have eq86 (X0 : G) : (e X0) = (e (v (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq17 eq83 | exact mod_symm (superpose eq17 eq83) | exact superpose eq83 eq17 | exact mod_symm (superpose eq83 eq17)
  have eq89 (X0 : G) : (e X0) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by first | exact superpose eq13 eq86 | exact mod_symm (superpose eq13 eq86) | exact superpose eq86 eq13 | exact mod_symm (superpose eq86 eq13)
  have eq101 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17) | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28)
  have eq105 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq101 | exact mod_symm (superpose eq17 eq101) | exact superpose eq101 eq17 | exact mod_symm (superpose eq101 eq17)
  have eq246 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ (e X1))))) = (e (v (X2 ◇ (e (X0 ◇ X1))))) := by first | exact superpose eq27 eq47 | exact mod_symm (superpose eq27 eq47) | exact superpose eq47 eq27 | exact mod_symm (superpose eq47 eq27)
  have eq247 (X0 X1 X2 : G) : (e (v (X2 ◇ (e (X0 ◇ X1))))) = (e (v (X2 ◇ ((e X0) ◇ X1)))) := by first | exact superpose eq28 eq47 | exact mod_symm (superpose eq28 eq47) | exact superpose eq47 eq28 | exact mod_symm (superpose eq47 eq28)
  have eq254 (X0 X1 : G) : (w X0 (e X1)) = (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq47 eq20 | exact mod_symm (superpose eq47 eq20) | exact superpose eq20 eq47 | exact mod_symm (superpose eq20 eq47)
  have eq276 (X0 X1 X2 : G) : (e (v (X2 ◇ ((e X0) ◇ X1)))) = (e (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq47 eq247 | exact mod_symm (superpose eq47 eq247) | exact superpose eq247 eq47 | exact mod_symm (superpose eq247 eq47)
  have eq277 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ (e X1))))) = (e (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq47 eq246 | exact mod_symm (superpose eq47 eq246) | exact superpose eq246 eq47 | exact mod_symm (superpose eq246 eq47)
  have eq295 (X0 X1 X2 : G) : ((e X2) ◇ (e (X0 ◇ X1))) = ((e X1) ◇ (e (X2 ◇ X0))) := by first | exact superpose eq14 eq31 | exact mod_symm (superpose eq14 eq31) | exact superpose eq31 eq14 | exact mod_symm (superpose eq31 eq14)
  have eq317 (X0 X1 X2 : G) : ((e X2) ◇ (e (X0 ◇ X1))) = (e (X1 ◇ (X2 ◇ X0))) := by first | exact superpose eq14 eq295 | exact mod_symm (superpose eq14 eq295) | exact superpose eq295 eq14 | exact mod_symm (superpose eq295 eq14)
  have eq334 (X0 X1 X2 : G) : (e (X2 ◇ (X0 ◇ X1))) = (e (X1 ◇ (X2 ◇ X0))) := by first | exact superpose eq14 eq317 | exact mod_symm (superpose eq14 eq317) | exact superpose eq317 eq14 | exact mod_symm (superpose eq317 eq14)
  have eq345 (X0 X1 X2 : G) : (e (v ((X0 ◇ (e X1)) ◇ X2))) = (e (v ((e (X0 ◇ X1)) ◇ X2))) := by first | exact superpose eq27 eq105 | exact mod_symm (superpose eq27 eq105) | exact superpose eq105 eq27 | exact mod_symm (superpose eq105 eq27)
  have eq346 (X0 X1 X2 : G) : (e (v ((e (X0 ◇ X1)) ◇ X2))) = (e (v (((e X0) ◇ X1) ◇ X2))) := by first | exact superpose eq28 eq105 | exact mod_symm (superpose eq28 eq105) | exact superpose eq105 eq28 | exact mod_symm (superpose eq105 eq28)
  have eq395 (X0 X1 X2 : G) : (e (v (((e X0) ◇ X1) ◇ X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq105 eq346 | exact mod_symm (superpose eq105 eq346) | exact superpose eq346 eq105 | exact mod_symm (superpose eq346 eq105)
  have eq396 (X0 X1 X2 : G) : (e (v ((X0 ◇ (e X1)) ◇ X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq105 eq345 | exact mod_symm (superpose eq105 eq345) | exact superpose eq345 eq105 | exact mod_symm (superpose eq345 eq105)
  have eq414 (X0 X1 X2 : G) : ((e (v X1)) ◇ (v (X2 ◇ X0))) = ((v X2) ◇ (v (X0 ◇ (e X1)))) := by first | exact superpose eq30 eq32 | exact mod_symm (superpose eq30 eq32) | exact superpose eq32 eq30 | exact mod_symm (superpose eq32 eq30)
  have eq416 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = ((v X3) ◇ (X0 ◇ (X1 ◇ (v X2)))) := by first | exact superpose eq13 eq32 | exact mod_symm (superpose eq13 eq32) | exact superpose eq32 eq13 | exact mod_symm (superpose eq32 eq13)
  have eq433 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e X1)))) = ((e (v X1)) ◇ (v (X2 ◇ X0))) := by first | exact superpose eq15 eq414 | exact mod_symm (superpose eq15 eq414) | exact superpose eq414 eq15 | exact mod_symm (superpose eq414 eq15)
  have eq444 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e X1)))) = (v ((e X1) ◇ (X2 ◇ X0))) := by first | exact superpose eq29 eq433 | exact mod_symm (superpose eq29 eq433) | exact superpose eq433 eq29 | exact mod_symm (superpose eq433 eq29)
  have eq614 (X0 X1 X2 X3 : G) : ((v X3) ◇ (X0 ◇ (v (X1 ◇ X2)))) = ((X0 ◇ (v X1)) ◇ (v (X3 ◇ X2))) := by first | exact superpose eq37 eq32 | exact mod_symm (superpose eq37 eq32) | exact superpose eq32 eq37 | exact mod_symm (superpose eq32 eq37)
  have eq621 (X0 X1 X2 X3 : G) : (X0 ◇ (v ((X1 ◇ X2) ◇ X3))) = ((X0 ◇ (v X1)) ◇ (v (X3 ◇ X2))) := by first | exact superpose eq37 eq614 | exact mod_symm (superpose eq37 eq614) | exact superpose eq614 eq37 | exact mod_symm (superpose eq614 eq37)
  have eq706 (X0 X1 X2 : G) : ((v (e X0)) ◇ ((((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0)))) ◇ X1) ◇ X2)) = (X2 ◇ (X1 ◇ (e X0))) := by first | exact superpose eq18 eq33 | exact mod_symm (superpose eq18 eq33) | exact superpose eq33 eq18 | exact mod_symm (superpose eq33 eq18)
  have eq707 (X0 X1 X2 X3 X4 : G) : ((v X1) ◇ ((((v X2) ◇ X0) ◇ X3) ◇ X4)) = (X4 ◇ (X3 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq32 eq33 | exact mod_symm (superpose eq32 eq33) | exact superpose eq33 eq32 | exact mod_symm (superpose eq33 eq32)
  have eq739 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X1) ◇ X0) ◇ (v (X4 ◇ X2))) = ((v X4) ◇ (X0 ◇ (X1 ◇ ((v X2) ◇ X3)))) := by first | exact superpose eq33 eq32 | exact mod_symm (superpose eq33 eq32) | exact superpose eq32 eq33 | exact mod_symm (superpose eq32 eq33)
  have eq740 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by first | exact superpose eq33 eq13 | exact mod_symm (superpose eq33 eq13) | exact superpose eq13 eq33 | exact mod_symm (superpose eq13 eq33)
  have eq750 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ (e X3))))) := by first | exact superpose eq33 eq105 | exact mod_symm (superpose eq33 eq105) | exact superpose eq105 eq33 | exact mod_symm (superpose eq105 eq33)
  have eq753 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = (X0 ◇ ((X1 ◇ (v X2)) ◇ (v X3))) := by first | exact superpose eq33 eq32 | exact mod_symm (superpose eq33 eq32) | exact superpose eq32 eq33 | exact mod_symm (superpose eq32 eq33)
  have eq758 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by first | exact superpose eq277 eq750 | exact mod_symm (superpose eq277 eq750) | exact superpose eq750 eq277 | exact mod_symm (superpose eq750 eq277)
  have eq774 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = (X2 ◇ (X1 ◇ (((v (e X0)) ◇ (v (e X0))) ◇ (v ((e X0) ◇ (e X0)))))) := by first | exact superpose eq707 eq706 | exact mod_symm (superpose eq707 eq706) | exact superpose eq706 eq707 | exact mod_symm (superpose eq706 eq707)
  have eq805 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = (X2 ◇ ((X1 ◇ (v (e X0))) ◇ (v (((e X0) ◇ (e X0)) ◇ (e X0))))) := by first | exact superpose eq753 eq774 | exact mod_symm (superpose eq753 eq774) | exact superpose eq774 eq753 | exact mod_symm (superpose eq774 eq753)
  have eq823 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v ((((e X0) ◇ (e X0)) ◇ (e X0)) ◇ (e X0)))) := by first | exact superpose eq753 eq805 | exact mod_symm (superpose eq753 eq805) | exact superpose eq805 eq753 | exact mod_symm (superpose eq805 eq753)
  have eq833 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v (((e (X0 ◇ X0)) ◇ (e X0)) ◇ (e X0)))) := by first | exact superpose eq14 eq823 | exact mod_symm (superpose eq14 eq823) | exact superpose eq823 eq14 | exact mod_symm (superpose eq823 eq14)
  have eq840 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v ((e ((X0 ◇ X0) ◇ X0)) ◇ (e X0)))) := by first | exact superpose eq14 eq833 | exact mod_symm (superpose eq14 eq833) | exact superpose eq833 eq14 | exact mod_symm (superpose eq833 eq14)
  have eq844 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v (e (((X0 ◇ X0) ◇ X0) ◇ X0)))) := by first | exact superpose eq14 eq840 | exact mod_symm (superpose eq14 eq840) | exact superpose eq840 eq14 | exact mod_symm (superpose eq840 eq14)
  have eq848 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (e (v (((X0 ◇ X0) ◇ X0) ◇ X0)))) := by first | exact superpose eq17 eq844 | exact mod_symm (superpose eq17 eq844) | exact superpose eq844 eq17 | exact mod_symm (superpose eq844 eq17)
  have eq852 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (w X0 X0)) := by first | exact superpose eq20 eq848 | exact mod_symm (superpose eq20 eq848) | exact superpose eq848 eq20 | exact mod_symm (superpose eq848 eq20)
  have eq926 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ X1)))) = (v (e (X0 ◇ (X1 ◇ X2)))) := by first | exact superpose eq334 eq17 | exact mod_symm (superpose eq334 eq17) | exact superpose eq17 eq334 | exact mod_symm (superpose eq17 eq334)
  have eq949 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ X1)))) = (e (v (X0 ◇ (X1 ◇ X2)))) := by first | exact superpose eq17 eq926 | exact mod_symm (superpose eq17 eq926) | exact superpose eq926 eq17 | exact mod_symm (superpose eq926 eq17)
  have eq1055 (X0 X1 X2 X3 X4 : G) : (((v X2) ◇ X0) ◇ ((X4 ◇ (v X1)) ◇ X3)) = (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq32 eq34 | exact mod_symm (superpose eq32 eq34) | exact superpose eq34 eq32 | exact mod_symm (superpose eq34 eq32)
  have eq1152 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ ((X1 ◇ X2) ◇ X0)))) = (e (v (X0 ◇ (X1 ◇ (X2 ◇ (e X3)))))) := by first | exact superpose eq34 eq105 | exact mod_symm (superpose eq34 eq105) | exact superpose eq105 eq34 | exact mod_symm (superpose eq105 eq34)
  have eq1208 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = ((v X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ (v X1)))) := by first | exact superpose eq740 eq1055 | exact mod_symm (superpose eq740 eq1055) | exact superpose eq1055 eq740 | exact mod_symm (superpose eq1055 eq740)
  have eq1242 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = (((X0 ◇ X3) ◇ X4) ◇ (v (X2 ◇ X1))) := by first | exact superpose eq416 eq1208 | exact mod_symm (superpose eq416 eq1208) | exact superpose eq1208 eq416 | exact mod_symm (superpose eq1208 eq416)
  have eq1888 (X0 X1 X2 X3 : G) : (e (v (((X0 ◇ (e X1)) ◇ X2) ◇ X3))) = (e (v ((e ((X0 ◇ X1) ◇ X2)) ◇ X3))) := by first | exact superpose eq48 eq105 | exact mod_symm (superpose eq48 eq105) | exact superpose eq105 eq48 | exact mod_symm (superpose eq105 eq48)
  have eq1889 (X0 X1 X2 X3 : G) : (e (v (((X0 ◇ (e X1)) ◇ X2) ◇ X3))) = (e (v (((X0 ◇ X1) ◇ X2) ◇ X3))) := by first | exact superpose eq105 eq1888 | exact mod_symm (superpose eq105 eq1888) | exact superpose eq1888 eq105 | exact mod_symm (superpose eq1888 eq105)
  have eq2020 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = ((v (e X0)) ◇ (X1 ◇ (X2 ◇ ((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0))))))) := by first | exact superpose eq18 eq39 | exact mod_symm (superpose eq18 eq39) | exact superpose eq39 eq18 | exact mod_symm (superpose eq39 eq18)
  have eq2183 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = (((((v (e X0)) ◇ (v (e X0))) ◇ X2) ◇ X1) ◇ (v ((e X0) ◇ (e X0)))) := by first | exact superpose eq739 eq2020 | exact mod_symm (superpose eq739 eq2020) | exact superpose eq2020 eq739 | exact mod_symm (superpose eq2020 eq739)
  have eq2289 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (((v (e X0)) ◇ (v (e X0))) ◇ (v ((e X0) ◇ (e X0)))))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1242 eq2183 | exact mod_symm (superpose eq1242 eq2183) | exact superpose eq2183 eq1242 | exact mod_symm (superpose eq2183 eq1242)
  have eq2338 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (v (e X0))) ◇ (v (((e X0) ◇ (e X0)) ◇ (e X0))))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq753 eq2289 | exact mod_symm (superpose eq753 eq2289) | exact superpose eq2289 eq753 | exact mod_symm (superpose eq2289 eq753)
  have eq2359 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v ((((e X0) ◇ (e X0)) ◇ (e X0)) ◇ (e X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq753 eq2338 | exact mod_symm (superpose eq753 eq2338) | exact superpose eq2338 eq753 | exact mod_symm (superpose eq2338 eq753)
  have eq2370 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v (((e (X0 ◇ X0)) ◇ (e X0)) ◇ (e X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq14 eq2359 | exact mod_symm (superpose eq14 eq2359) | exact superpose eq2359 eq14 | exact mod_symm (superpose eq2359 eq14)
  have eq2377 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v ((e ((X0 ◇ X0) ◇ X0)) ◇ (e X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq14 eq2370 | exact mod_symm (superpose eq14 eq2370) | exact superpose eq2370 eq14 | exact mod_symm (superpose eq2370 eq14)
  have eq2382 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v (e (((X0 ◇ X0) ◇ X0) ◇ X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq14 eq2377 | exact mod_symm (superpose eq14 eq2377) | exact superpose eq2377 eq14 | exact mod_symm (superpose eq2377 eq14)
  have eq2386 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (e (v (((X0 ◇ X0) ◇ X0) ◇ X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq17 eq2382 | exact mod_symm (superpose eq17 eq2382) | exact superpose eq2382 eq17 | exact mod_symm (superpose eq2382 eq17)
  have eq2389 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (w X0 X0)) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq20 eq2386 | exact mod_symm (superpose eq20 eq2386) | exact superpose eq2386 eq20 | exact mod_symm (superpose eq2386 eq20)
  have eq2391 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq852 eq2389 | exact mod_symm (superpose eq852 eq2389) | exact superpose eq2389 eq852 | exact mod_symm (superpose eq2389 eq852)
  have eq2410 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0)))) ◇ ((v (e X0)) ◇ (e X1))) := by first | exact superpose eq18 eq2391 | exact mod_symm (superpose eq18 eq2391) | exact superpose eq2391 eq18 | exact mod_symm (superpose eq2391 eq18)
  have eq2428 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (X0 ◇ (e X1))) ◇ (e X1)))) := by first | exact superpose eq2391 eq20 | exact mod_symm (superpose eq2391 eq20) | exact superpose eq20 eq2391 | exact mod_symm (superpose eq20 eq2391)
  have eq2429 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((e X0) ◇ ((X1 ◇ X1) ◇ (e X0))))) := by first | exact superpose eq2391 eq20 | exact mod_symm (superpose eq2391 eq20) | exact superpose eq20 eq2391 | exact mod_symm (superpose eq20 eq2391)
  have eq2435 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ (e X2))))) = (e (v ((X1 ◇ X0) ◇ X2))) := by first | exact superpose eq2391 eq47 | exact mod_symm (superpose eq2391 eq47) | exact superpose eq47 eq2391 | exact mod_symm (superpose eq47 eq2391)
  have eq2466 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ X2)))) = (e (v ((X1 ◇ X0) ◇ X2))) := by first | exact superpose eq277 eq2435 | exact mod_symm (superpose eq277 eq2435) | exact superpose eq2435 eq277 | exact mod_symm (superpose eq2435 eq277)
  have eq2470 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((e X0) ◇ ((X1 ◇ X1) ◇ X0)))) := by first | exact superpose eq277 eq2429 | exact mod_symm (superpose eq277 eq2429) | exact superpose eq2429 eq277 | exact mod_symm (superpose eq2429 eq277)
  have eq2471 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (X0 ◇ (e X1))) ◇ X1))) := by first | exact superpose eq47 eq2428 | exact mod_symm (superpose eq47 eq2428) | exact superpose eq2428 eq47 | exact mod_symm (superpose eq2428 eq47)
  have eq2476 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((v (e X0)) ◇ ((e X1) ◇ ((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0)))))) := by first | exact superpose eq13 eq2410 | exact mod_symm (superpose eq13 eq2410) | exact superpose eq2410 eq13 | exact mod_symm (superpose eq2410 eq13)
  have eq2505 (X0 X1 : G) : (w X1 (e X0)) = (e (v (X0 ◇ ((e X0) ◇ (X1 ◇ X1))))) := by first | exact superpose eq949 eq2470 | exact mod_symm (superpose eq949 eq2470) | exact superpose eq2470 eq949 | exact mod_symm (superpose eq2470 eq949)
  have eq2506 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (e X1)) ◇ (X0 ◇ X1)))) := by first | exact superpose eq2466 eq2471 | exact mod_symm (superpose eq2466 eq2471) | exact superpose eq2471 eq2466 | exact mod_symm (superpose eq2471 eq2466)
  have eq2510 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((((v (e X0)) ◇ (v (e X0))) ◇ (e X1)) ◇ (v ((e X0) ◇ (e X0)))) := by first | exact superpose eq739 eq2476 | exact mod_symm (superpose eq739 eq2476) | exact superpose eq2476 eq739 | exact mod_symm (superpose eq2476 eq739)
  have eq2530 (X0 X1 : G) : (w X1 (e X0)) = (e (v (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq276 eq2505 | exact mod_symm (superpose eq276 eq2505) | exact superpose eq2505 eq276 | exact mod_symm (superpose eq2505 eq276)
  have eq2531 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by first | exact superpose eq396 eq2506 | exact mod_symm (superpose eq396 eq2506) | exact superpose eq2506 eq396 | exact mod_symm (superpose eq2506 eq396)
  have eq2535 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((v (e X0)) ◇ ((e X1) ◇ ((v (e X0)) ◇ (v ((e X0) ◇ (e X0)))))) := by first | exact superpose eq1242 eq2510 | exact mod_symm (superpose eq1242 eq2510) | exact superpose eq2510 eq1242 | exact mod_symm (superpose eq2510 eq1242)
  have eq2552 (X0 X1 : G) : (w X0 (e X1)) = (e (v (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by first | exact superpose eq2466 eq2531 | exact mod_symm (superpose eq2466 eq2531) | exact superpose eq2531 eq2466 | exact mod_symm (superpose eq2531 eq2466)
  have eq2554 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (((e X1) ◇ (v (e X0))) ◇ (v ((e X0) ◇ ((e X0) ◇ (e X0))))) := by first | exact superpose eq416 eq2535 | exact mod_symm (superpose eq416 eq2535) | exact superpose eq2535 eq416 | exact mod_symm (superpose eq2535 eq416)
  have eq2566 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (v (((e X0) ◇ ((e X0) ◇ (e X0))) ◇ (e X0)))) := by first | exact superpose eq621 eq2554 | exact mod_symm (superpose eq621 eq2554) | exact superpose eq2554 eq621 | exact mod_symm (superpose eq2554 eq621)
  have eq2578 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (v (((e X0) ◇ (e X0)) ◇ ((e X0) ◇ (e X0))))) := by first | exact superpose eq2391 eq2566 | exact mod_symm (superpose eq2391 eq2566) | exact superpose eq2566 eq2391 | exact mod_symm (superpose eq2566 eq2391)
  have eq2585 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (v ((e X0) ◇ (((e X0) ◇ (e X0)) ◇ (e X0))))) := by first | exact superpose eq444 eq2578 | exact mod_symm (superpose eq444 eq2578) | exact superpose eq2578 eq444 | exact mod_symm (superpose eq2578 eq444)
  have eq2588 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (v ((e X0) ◇ ((e X0) ◇ ((e X0) ◇ (e X0)))))) := by first | exact superpose eq444 eq2585 | exact mod_symm (superpose eq444 eq2585) | exact superpose eq2585 eq444 | exact mod_symm (superpose eq2585 eq444)
  have eq2589 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (e X0)) := by first | exact superpose eq19 eq2588 | exact mod_symm (superpose eq19 eq2588) | exact superpose eq2588 eq19 | exact mod_symm (superpose eq2588 eq19)
  have eq2590 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq2589 | exact mod_symm (superpose eq14 eq2589) | exact superpose eq2589 eq14 | exact mod_symm (superpose eq2589 eq14)
  have eq2606 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((e (X0 ◇ (e X0))) ◇ X1) ◇ X1))) := by first | exact superpose eq28 eq52 | exact mod_symm (superpose eq28 eq52) | exact superpose eq52 eq28 | exact mod_symm (superpose eq52 eq28)
  have eq2610 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e ((X0 ◇ X0) ◇ X1)) ◇ (e X1)))) := by first | exact superpose eq14 eq52 | exact mod_symm (superpose eq14 eq52) | exact superpose eq52 eq14 | exact mod_symm (superpose eq52 eq14)
  have eq2634 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (((e (X0 ◇ X0)) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq52 eq47 | exact mod_symm (superpose eq52 eq47) | exact superpose eq47 eq52 | exact mod_symm (superpose eq47 eq52)
  have eq2661 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq395 eq2634 | exact mod_symm (superpose eq395 eq2634) | exact superpose eq2634 eq395 | exact mod_symm (superpose eq2634 eq395)
  have eq2684 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e ((X0 ◇ X0) ◇ X1)) ◇ X1))) := by first | exact superpose eq47 eq2610 | exact mod_symm (superpose eq47 eq2610) | exact superpose eq2610 eq47 | exact mod_symm (superpose eq2610 eq47)
  have eq2688 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((X0 ◇ (e X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq395 eq2606 | exact mod_symm (superpose eq395 eq2606) | exact superpose eq2606 eq395 | exact mod_symm (superpose eq2606 eq395)
  have eq2708 (X0 X1 : G) : (w X0 (e X1)) = (w (e X0) (e X1)) := by first | exact superpose eq254 eq2661 | exact mod_symm (superpose eq254 eq2661) | exact superpose eq2661 eq254 | exact mod_symm (superpose eq2661 eq254)
  have eq2731 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq105 eq2684 | exact mod_symm (superpose eq105 eq2684) | exact superpose eq2684 eq105 | exact mod_symm (superpose eq2684 eq105)
  have eq2735 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e (e X0)) X1) := by first | exact superpose eq1889 eq2688 | exact mod_symm (superpose eq1889 eq2688) | exact superpose eq2688 eq1889 | exact mod_symm (superpose eq2688 eq1889)
  have eq2771 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w X0 (e X1)) := by first | exact superpose eq2708 eq2731 | exact mod_symm (superpose eq2708 eq2731) | exact superpose eq2731 eq2708 | exact mod_symm (superpose eq2731 eq2708)
  have eq2775 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e X0) X1) := by first | exact superpose eq16 eq2735 | exact mod_symm (superpose eq16 eq2735) | exact superpose eq2735 eq16 | exact mod_symm (superpose eq2735 eq16)
  have eq2797 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq20 eq2771 | exact mod_symm (superpose eq20 eq2771) | exact superpose eq2771 eq20 | exact mod_symm (superpose eq2771 eq20)
  have eq2801 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq20 eq2775 | exact mod_symm (superpose eq20 eq2775) | exact superpose eq2775 eq20 | exact mod_symm (superpose eq2775 eq20)
  have eq3978 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e (X0 ◇ (X1 ◇ X1))) ◇ (e X0)))) := by first | exact superpose eq2590 eq52 | exact mod_symm (superpose eq2590 eq52) | exact superpose eq52 eq2590 | exact mod_symm (superpose eq52 eq2590)
  have eq3991 (X0 : G) : (e (e X0)) = (e (v ((e X0) ◇ ((e X0) ◇ (e (X0 ◇ X0)))))) := by first | exact superpose eq2590 eq89 | exact mod_symm (superpose eq2590 eq89) | exact superpose eq89 eq2590 | exact mod_symm (superpose eq89 eq2590)
  have eq4022 (X0 : G) : (e (e X0)) = (e (v ((e X0) ◇ ((e X0) ◇ (X0 ◇ X0))))) := by first | exact superpose eq277 eq3991 | exact mod_symm (superpose eq277 eq3991) | exact superpose eq3991 eq277 | exact mod_symm (superpose eq3991 eq277)
  have eq4033 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e (X0 ◇ (X1 ◇ X1))) ◇ X0))) := by first | exact superpose eq47 eq3978 | exact mod_symm (superpose eq47 eq3978) | exact superpose eq3978 eq47 | exact mod_symm (superpose eq3978 eq47)
  have eq4069 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ ((X0 ◇ (e X0)) ◇ (e X0))))) := by first | exact superpose eq758 eq4022 | exact mod_symm (superpose eq758 eq4022) | exact superpose eq4022 eq758 | exact mod_symm (superpose eq4022 eq758)
  have eq4080 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by first | exact superpose eq105 eq4033 | exact mod_symm (superpose eq105 eq4033) | exact superpose eq4033 eq105 | exact mod_symm (superpose eq4033 eq105)
  have eq4097 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ ((X0 ◇ (e X0)) ◇ X0)))) := by first | exact superpose eq277 eq4069 | exact mod_symm (superpose eq277 eq4069) | exact superpose eq4069 eq277 | exact mod_symm (superpose eq4069 eq277)
  have eq4105 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := by first | exact superpose eq2466 eq4080 | exact mod_symm (superpose eq2466 eq4080) | exact superpose eq4080 eq2466 | exact mod_symm (superpose eq4080 eq2466)
  have eq4114 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ (e X0)))))) := by first | exact superpose eq949 eq4097 | exact mod_symm (superpose eq949 eq4097) | exact superpose eq4097 eq949 | exact mod_symm (superpose eq4097 eq949)
  have eq4118 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by first | exact superpose eq2466 eq4105 | exact mod_symm (superpose eq2466 eq4105) | exact superpose eq4105 eq2466 | exact mod_symm (superpose eq4105 eq2466)
  have eq4121 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq1152 eq4114 | exact mod_symm (superpose eq1152 eq4114) | exact superpose eq4114 eq1152 | exact mod_symm (superpose eq4114 eq1152)
  have eq4125 (X0 X1 : G) : (w X0 (e X1)) = (w (e X1) (e X0)) := by first | exact superpose eq2530 eq4118 | exact mod_symm (superpose eq2530 eq4118) | exact superpose eq4118 eq2530 | exact mod_symm (superpose eq4118 eq2530)
  have eq4126 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by first | exact superpose eq949 eq4121 | exact mod_symm (superpose eq949 eq4121) | exact superpose eq4121 eq949 | exact mod_symm (superpose eq4121 eq949)
  have eq4127 (X0 X1 : G) : (w X0 (e X1)) = (w (e X1) X0) := by first | exact superpose eq2797 eq4125 | exact mod_symm (superpose eq2797 eq4125) | exact superpose eq4125 eq2797 | exact mod_symm (superpose eq4125 eq2797)
  have eq4128 (X0 : G) : (e (e X0)) = (w X0 (e X0)) := by first | exact superpose eq2552 eq4126 | exact mod_symm (superpose eq2552 eq4126) | exact superpose eq4126 eq2552 | exact mod_symm (superpose eq4126 eq2552)
  have eq4129 (X0 X1 : G) : (w X0 (e X1)) = (w X1 X0) := by first | exact superpose eq2801 eq4127 | exact mod_symm (superpose eq2801 eq4127) | exact superpose eq4127 eq2801 | exact mod_symm (superpose eq4127 eq2801)
  have eq4130 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq2797 eq4128 | exact mod_symm (superpose eq2797 eq4128) | exact superpose eq4128 eq2797 | exact mod_symm (superpose eq4128 eq2797)
  have eq4131 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq16 eq4130 | exact mod_symm (superpose eq16 eq4130) | exact superpose eq4130 eq16 | exact mod_symm (superpose eq4130 eq16)
  have eq4466 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq4131 eq21 | exact mod_symm (superpose eq4131 eq21) | exact superpose eq21 eq4131 | exact mod_symm (superpose eq21 eq4131)
  subsumption eq4466 eq4129


/-- Equation 4343 `x ◇ (y ◇ y) = y ◇ (x ◇ x)` is term-definable from equation 4364 over finite magmas, via the term
`x □ y := u^[2N+1] (((x ◇ x) ◇ y) ◇ y)` with `u a = (a ◇ (a ◇ (a ◇ a)))`. -/
private theorem aux4364_4343 [Magma G] (h : Equation4364 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, ((v (e a)) ◇ ((v (e a)) ◇ ((v (e a)) ◇ (v (e a))))) = e a)
    (hvue : ∀ a : G, v ((e a) ◇ ((e a) ◇ ((e a) ◇ (e a)))) = e a)
    (hw : ∀ a b : G, w a b = (e (v ((((a ◇ a) ◇ b) ◇ b)))))
    (x y : G) :
    (w x (w y y)) =
      (w y (w x x)) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ ((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0))))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ ((e X0) ◇ ((e X0) ◇ (e X0))))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) := mod_symm (hw ..)
  have eq21 : (w x (w y y)) ≠ (w y (w x x)) := mod_symm nh
  have eq25 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq26 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq28 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq25 | exact mod_symm (superpose eq14 eq25) | exact superpose eq25 eq14 | exact mod_symm (superpose eq25 eq14)
  have eq29 (X0 X1 : G) : (v ((e X0) ◇ X1)) = ((e (v X0)) ◇ (v X1)) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq30 (X0 X1 : G) : (v (X1 ◇ (e X0))) = ((v X1) ◇ (e (v X0))) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq31 (X0 X1 X2 : G) : ((e X0) ◇ ((e X1) ◇ X2)) = (X2 ◇ (e (X0 ◇ X1))) := by first | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13) | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14)
  have eq32 (X0 X1 X2 : G) : ((v X0) ◇ ((v X1) ◇ X2)) = (X2 ◇ (v (X0 ◇ X1))) := by first | exact superpose eq15 eq13 | exact mod_symm (superpose eq15 eq13) | exact superpose eq13 eq15 | exact mod_symm (superpose eq13 eq15)
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq34 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq36 (X0 X1 X2 : G) : (X2 ◇ (e (X0 ◇ X1))) = ((e X1) ◇ (X2 ◇ (e X0))) := by first | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13) | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14)
  have eq37 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ (X2 ◇ (v X0))) := by first | exact superpose eq15 eq13 | exact mod_symm (superpose eq15 eq13) | exact superpose eq13 eq15 | exact mod_symm (superpose eq13 eq15)
  have eq39 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq44 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = ((e (X0 ◇ X1)) ◇ (e X2)) := by first | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14) | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27)
  have eq45 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq27 eq17 | exact mod_symm (superpose eq27 eq17) | exact superpose eq17 eq27 | exact mod_symm (superpose eq17 eq27)
  have eq47 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq45 | exact mod_symm (superpose eq17 eq45) | exact superpose eq45 eq17 | exact mod_symm (superpose eq45 eq17)
  have eq48 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = (e ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq14 eq44 | exact mod_symm (superpose eq14 eq44) | exact superpose eq44 eq14 | exact mod_symm (superpose eq44 eq14)
  have eq52 (X0 X1 : G) : (w (e X0) X1) = (e (v (((e (X0 ◇ X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq75 (X0 : G) : (e X0) = (v ((e X0) ◇ ((e X0) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq80 (X0 : G) : (e X0) = (v ((e X0) ◇ (e ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq36 eq75 | exact mod_symm (superpose eq36 eq75) | exact superpose eq75 eq36 | exact mod_symm (superpose eq75 eq36)
  have eq83 (X0 : G) : (e X0) = (v (e (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq14 eq80 | exact mod_symm (superpose eq14 eq80) | exact superpose eq80 eq14 | exact mod_symm (superpose eq80 eq14)
  have eq86 (X0 : G) : (e X0) = (e (v (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq17 eq83 | exact mod_symm (superpose eq17 eq83) | exact superpose eq83 eq17 | exact mod_symm (superpose eq83 eq17)
  have eq89 (X0 : G) : (e X0) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by first | exact superpose eq13 eq86 | exact mod_symm (superpose eq13 eq86) | exact superpose eq86 eq13 | exact mod_symm (superpose eq86 eq13)
  have eq101 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17) | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28)
  have eq105 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq101 | exact mod_symm (superpose eq17 eq101) | exact superpose eq101 eq17 | exact mod_symm (superpose eq101 eq17)
  have eq246 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ (e X1))))) = (e (v (X2 ◇ (e (X0 ◇ X1))))) := by first | exact superpose eq27 eq47 | exact mod_symm (superpose eq27 eq47) | exact superpose eq47 eq27 | exact mod_symm (superpose eq47 eq27)
  have eq247 (X0 X1 X2 : G) : (e (v (X2 ◇ (e (X0 ◇ X1))))) = (e (v (X2 ◇ ((e X0) ◇ X1)))) := by first | exact superpose eq28 eq47 | exact mod_symm (superpose eq28 eq47) | exact superpose eq47 eq28 | exact mod_symm (superpose eq47 eq28)
  have eq254 (X0 X1 : G) : (w X0 (e X1)) = (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq47 eq20 | exact mod_symm (superpose eq47 eq20) | exact superpose eq20 eq47 | exact mod_symm (superpose eq20 eq47)
  have eq276 (X0 X1 X2 : G) : (e (v (X2 ◇ ((e X0) ◇ X1)))) = (e (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq47 eq247 | exact mod_symm (superpose eq47 eq247) | exact superpose eq247 eq47 | exact mod_symm (superpose eq247 eq47)
  have eq277 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ (e X1))))) = (e (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq47 eq246 | exact mod_symm (superpose eq47 eq246) | exact superpose eq246 eq47 | exact mod_symm (superpose eq246 eq47)
  have eq295 (X0 X1 X2 : G) : ((e X2) ◇ (e (X0 ◇ X1))) = ((e X1) ◇ (e (X2 ◇ X0))) := by first | exact superpose eq14 eq31 | exact mod_symm (superpose eq14 eq31) | exact superpose eq31 eq14 | exact mod_symm (superpose eq31 eq14)
  have eq317 (X0 X1 X2 : G) : ((e X2) ◇ (e (X0 ◇ X1))) = (e (X1 ◇ (X2 ◇ X0))) := by first | exact superpose eq14 eq295 | exact mod_symm (superpose eq14 eq295) | exact superpose eq295 eq14 | exact mod_symm (superpose eq295 eq14)
  have eq334 (X0 X1 X2 : G) : (e (X2 ◇ (X0 ◇ X1))) = (e (X1 ◇ (X2 ◇ X0))) := by first | exact superpose eq14 eq317 | exact mod_symm (superpose eq14 eq317) | exact superpose eq317 eq14 | exact mod_symm (superpose eq317 eq14)
  have eq345 (X0 X1 X2 : G) : (e (v ((X0 ◇ (e X1)) ◇ X2))) = (e (v ((e (X0 ◇ X1)) ◇ X2))) := by first | exact superpose eq27 eq105 | exact mod_symm (superpose eq27 eq105) | exact superpose eq105 eq27 | exact mod_symm (superpose eq105 eq27)
  have eq346 (X0 X1 X2 : G) : (e (v ((e (X0 ◇ X1)) ◇ X2))) = (e (v (((e X0) ◇ X1) ◇ X2))) := by first | exact superpose eq28 eq105 | exact mod_symm (superpose eq28 eq105) | exact superpose eq105 eq28 | exact mod_symm (superpose eq105 eq28)
  have eq395 (X0 X1 X2 : G) : (e (v (((e X0) ◇ X1) ◇ X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq105 eq346 | exact mod_symm (superpose eq105 eq346) | exact superpose eq346 eq105 | exact mod_symm (superpose eq346 eq105)
  have eq396 (X0 X1 X2 : G) : (e (v ((X0 ◇ (e X1)) ◇ X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq105 eq345 | exact mod_symm (superpose eq105 eq345) | exact superpose eq345 eq105 | exact mod_symm (superpose eq345 eq105)
  have eq414 (X0 X1 X2 : G) : ((e (v X1)) ◇ (v (X2 ◇ X0))) = ((v X2) ◇ (v (X0 ◇ (e X1)))) := by first | exact superpose eq30 eq32 | exact mod_symm (superpose eq30 eq32) | exact superpose eq32 eq30 | exact mod_symm (superpose eq32 eq30)
  have eq416 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = ((v X3) ◇ (X0 ◇ (X1 ◇ (v X2)))) := by first | exact superpose eq13 eq32 | exact mod_symm (superpose eq13 eq32) | exact superpose eq32 eq13 | exact mod_symm (superpose eq32 eq13)
  have eq433 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e X1)))) = ((e (v X1)) ◇ (v (X2 ◇ X0))) := by first | exact superpose eq15 eq414 | exact mod_symm (superpose eq15 eq414) | exact superpose eq414 eq15 | exact mod_symm (superpose eq414 eq15)
  have eq444 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e X1)))) = (v ((e X1) ◇ (X2 ◇ X0))) := by first | exact superpose eq29 eq433 | exact mod_symm (superpose eq29 eq433) | exact superpose eq433 eq29 | exact mod_symm (superpose eq433 eq29)
  have eq614 (X0 X1 X2 X3 : G) : ((v X3) ◇ (X0 ◇ (v (X1 ◇ X2)))) = ((X0 ◇ (v X1)) ◇ (v (X3 ◇ X2))) := by first | exact superpose eq37 eq32 | exact mod_symm (superpose eq37 eq32) | exact superpose eq32 eq37 | exact mod_symm (superpose eq32 eq37)
  have eq621 (X0 X1 X2 X3 : G) : (X0 ◇ (v ((X1 ◇ X2) ◇ X3))) = ((X0 ◇ (v X1)) ◇ (v (X3 ◇ X2))) := by first | exact superpose eq37 eq614 | exact mod_symm (superpose eq37 eq614) | exact superpose eq614 eq37 | exact mod_symm (superpose eq614 eq37)
  have eq706 (X0 X1 X2 : G) : ((v (e X0)) ◇ ((((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0)))) ◇ X1) ◇ X2)) = (X2 ◇ (X1 ◇ (e X0))) := by first | exact superpose eq18 eq33 | exact mod_symm (superpose eq18 eq33) | exact superpose eq33 eq18 | exact mod_symm (superpose eq33 eq18)
  have eq707 (X0 X1 X2 X3 X4 : G) : ((v X1) ◇ ((((v X2) ◇ X0) ◇ X3) ◇ X4)) = (X4 ◇ (X3 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq32 eq33 | exact mod_symm (superpose eq32 eq33) | exact superpose eq33 eq32 | exact mod_symm (superpose eq33 eq32)
  have eq739 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X1) ◇ X0) ◇ (v (X4 ◇ X2))) = ((v X4) ◇ (X0 ◇ (X1 ◇ ((v X2) ◇ X3)))) := by first | exact superpose eq33 eq32 | exact mod_symm (superpose eq33 eq32) | exact superpose eq32 eq33 | exact mod_symm (superpose eq32 eq33)
  have eq740 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by first | exact superpose eq33 eq13 | exact mod_symm (superpose eq33 eq13) | exact superpose eq13 eq33 | exact mod_symm (superpose eq13 eq33)
  have eq750 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ (e X3))))) := by first | exact superpose eq33 eq105 | exact mod_symm (superpose eq33 eq105) | exact superpose eq105 eq33 | exact mod_symm (superpose eq105 eq33)
  have eq753 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = (X0 ◇ ((X1 ◇ (v X2)) ◇ (v X3))) := by first | exact superpose eq33 eq32 | exact mod_symm (superpose eq33 eq32) | exact superpose eq32 eq33 | exact mod_symm (superpose eq32 eq33)
  have eq758 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by first | exact superpose eq277 eq750 | exact mod_symm (superpose eq277 eq750) | exact superpose eq750 eq277 | exact mod_symm (superpose eq750 eq277)
  have eq774 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = (X2 ◇ (X1 ◇ (((v (e X0)) ◇ (v (e X0))) ◇ (v ((e X0) ◇ (e X0)))))) := by first | exact superpose eq707 eq706 | exact mod_symm (superpose eq707 eq706) | exact superpose eq706 eq707 | exact mod_symm (superpose eq706 eq707)
  have eq805 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = (X2 ◇ ((X1 ◇ (v (e X0))) ◇ (v (((e X0) ◇ (e X0)) ◇ (e X0))))) := by first | exact superpose eq753 eq774 | exact mod_symm (superpose eq753 eq774) | exact superpose eq774 eq753 | exact mod_symm (superpose eq774 eq753)
  have eq823 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v ((((e X0) ◇ (e X0)) ◇ (e X0)) ◇ (e X0)))) := by first | exact superpose eq753 eq805 | exact mod_symm (superpose eq753 eq805) | exact superpose eq805 eq753 | exact mod_symm (superpose eq805 eq753)
  have eq833 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v (((e (X0 ◇ X0)) ◇ (e X0)) ◇ (e X0)))) := by first | exact superpose eq14 eq823 | exact mod_symm (superpose eq14 eq823) | exact superpose eq823 eq14 | exact mod_symm (superpose eq823 eq14)
  have eq840 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v ((e ((X0 ◇ X0) ◇ X0)) ◇ (e X0)))) := by first | exact superpose eq14 eq833 | exact mod_symm (superpose eq14 eq833) | exact superpose eq833 eq14 | exact mod_symm (superpose eq833 eq14)
  have eq844 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v (e (((X0 ◇ X0) ◇ X0) ◇ X0)))) := by first | exact superpose eq14 eq840 | exact mod_symm (superpose eq14 eq840) | exact superpose eq840 eq14 | exact mod_symm (superpose eq840 eq14)
  have eq848 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (e (v (((X0 ◇ X0) ◇ X0) ◇ X0)))) := by first | exact superpose eq17 eq844 | exact mod_symm (superpose eq17 eq844) | exact superpose eq844 eq17 | exact mod_symm (superpose eq844 eq17)
  have eq852 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (w X0 X0)) := by first | exact superpose eq20 eq848 | exact mod_symm (superpose eq20 eq848) | exact superpose eq848 eq20 | exact mod_symm (superpose eq848 eq20)
  have eq926 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ X1)))) = (v (e (X0 ◇ (X1 ◇ X2)))) := by first | exact superpose eq334 eq17 | exact mod_symm (superpose eq334 eq17) | exact superpose eq17 eq334 | exact mod_symm (superpose eq17 eq334)
  have eq949 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ X1)))) = (e (v (X0 ◇ (X1 ◇ X2)))) := by first | exact superpose eq17 eq926 | exact mod_symm (superpose eq17 eq926) | exact superpose eq926 eq17 | exact mod_symm (superpose eq926 eq17)
  have eq1055 (X0 X1 X2 X3 X4 : G) : (((v X2) ◇ X0) ◇ ((X4 ◇ (v X1)) ◇ X3)) = (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq32 eq34 | exact mod_symm (superpose eq32 eq34) | exact superpose eq34 eq32 | exact mod_symm (superpose eq34 eq32)
  have eq1152 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ ((X1 ◇ X2) ◇ X0)))) = (e (v (X0 ◇ (X1 ◇ (X2 ◇ (e X3)))))) := by first | exact superpose eq34 eq105 | exact mod_symm (superpose eq34 eq105) | exact superpose eq105 eq34 | exact mod_symm (superpose eq105 eq34)
  have eq1208 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = ((v X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ (v X1)))) := by first | exact superpose eq740 eq1055 | exact mod_symm (superpose eq740 eq1055) | exact superpose eq1055 eq740 | exact mod_symm (superpose eq1055 eq740)
  have eq1242 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = (((X0 ◇ X3) ◇ X4) ◇ (v (X2 ◇ X1))) := by first | exact superpose eq416 eq1208 | exact mod_symm (superpose eq416 eq1208) | exact superpose eq1208 eq416 | exact mod_symm (superpose eq1208 eq416)
  have eq1888 (X0 X1 X2 X3 : G) : (e (v (((X0 ◇ (e X1)) ◇ X2) ◇ X3))) = (e (v ((e ((X0 ◇ X1) ◇ X2)) ◇ X3))) := by first | exact superpose eq48 eq105 | exact mod_symm (superpose eq48 eq105) | exact superpose eq105 eq48 | exact mod_symm (superpose eq105 eq48)
  have eq1889 (X0 X1 X2 X3 : G) : (e (v (((X0 ◇ (e X1)) ◇ X2) ◇ X3))) = (e (v (((X0 ◇ X1) ◇ X2) ◇ X3))) := by first | exact superpose eq105 eq1888 | exact mod_symm (superpose eq105 eq1888) | exact superpose eq1888 eq105 | exact mod_symm (superpose eq1888 eq105)
  have eq2020 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = ((v (e X0)) ◇ (X1 ◇ (X2 ◇ ((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0))))))) := by first | exact superpose eq18 eq39 | exact mod_symm (superpose eq18 eq39) | exact superpose eq39 eq18 | exact mod_symm (superpose eq39 eq18)
  have eq2183 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = (((((v (e X0)) ◇ (v (e X0))) ◇ X2) ◇ X1) ◇ (v ((e X0) ◇ (e X0)))) := by first | exact superpose eq739 eq2020 | exact mod_symm (superpose eq739 eq2020) | exact superpose eq2020 eq739 | exact mod_symm (superpose eq2020 eq739)
  have eq2289 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (((v (e X0)) ◇ (v (e X0))) ◇ (v ((e X0) ◇ (e X0)))))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1242 eq2183 | exact mod_symm (superpose eq1242 eq2183) | exact superpose eq2183 eq1242 | exact mod_symm (superpose eq2183 eq1242)
  have eq2338 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (v (e X0))) ◇ (v (((e X0) ◇ (e X0)) ◇ (e X0))))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq753 eq2289 | exact mod_symm (superpose eq753 eq2289) | exact superpose eq2289 eq753 | exact mod_symm (superpose eq2289 eq753)
  have eq2359 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v ((((e X0) ◇ (e X0)) ◇ (e X0)) ◇ (e X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq753 eq2338 | exact mod_symm (superpose eq753 eq2338) | exact superpose eq2338 eq753 | exact mod_symm (superpose eq2338 eq753)
  have eq2370 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v (((e (X0 ◇ X0)) ◇ (e X0)) ◇ (e X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq14 eq2359 | exact mod_symm (superpose eq14 eq2359) | exact superpose eq2359 eq14 | exact mod_symm (superpose eq2359 eq14)
  have eq2377 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v ((e ((X0 ◇ X0) ◇ X0)) ◇ (e X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq14 eq2370 | exact mod_symm (superpose eq14 eq2370) | exact superpose eq2370 eq14 | exact mod_symm (superpose eq2370 eq14)
  have eq2382 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v (e (((X0 ◇ X0) ◇ X0) ◇ X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq14 eq2377 | exact mod_symm (superpose eq14 eq2377) | exact superpose eq2377 eq14 | exact mod_symm (superpose eq2377 eq14)
  have eq2386 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (e (v (((X0 ◇ X0) ◇ X0) ◇ X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq17 eq2382 | exact mod_symm (superpose eq17 eq2382) | exact superpose eq2382 eq17 | exact mod_symm (superpose eq2382 eq17)
  have eq2389 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (w X0 X0)) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq20 eq2386 | exact mod_symm (superpose eq20 eq2386) | exact superpose eq2386 eq20 | exact mod_symm (superpose eq2386 eq20)
  have eq2391 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq852 eq2389 | exact mod_symm (superpose eq852 eq2389) | exact superpose eq2389 eq852 | exact mod_symm (superpose eq2389 eq852)
  have eq2410 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0)))) ◇ ((v (e X0)) ◇ (e X1))) := by first | exact superpose eq18 eq2391 | exact mod_symm (superpose eq18 eq2391) | exact superpose eq2391 eq18 | exact mod_symm (superpose eq2391 eq18)
  have eq2428 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (X0 ◇ (e X1))) ◇ (e X1)))) := by first | exact superpose eq2391 eq20 | exact mod_symm (superpose eq2391 eq20) | exact superpose eq20 eq2391 | exact mod_symm (superpose eq20 eq2391)
  have eq2429 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((e X0) ◇ ((X1 ◇ X1) ◇ (e X0))))) := by first | exact superpose eq2391 eq20 | exact mod_symm (superpose eq2391 eq20) | exact superpose eq20 eq2391 | exact mod_symm (superpose eq20 eq2391)
  have eq2435 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ (e X2))))) = (e (v ((X1 ◇ X0) ◇ X2))) := by first | exact superpose eq2391 eq47 | exact mod_symm (superpose eq2391 eq47) | exact superpose eq47 eq2391 | exact mod_symm (superpose eq47 eq2391)
  have eq2466 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ X2)))) = (e (v ((X1 ◇ X0) ◇ X2))) := by first | exact superpose eq277 eq2435 | exact mod_symm (superpose eq277 eq2435) | exact superpose eq2435 eq277 | exact mod_symm (superpose eq2435 eq277)
  have eq2470 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((e X0) ◇ ((X1 ◇ X1) ◇ X0)))) := by first | exact superpose eq277 eq2429 | exact mod_symm (superpose eq277 eq2429) | exact superpose eq2429 eq277 | exact mod_symm (superpose eq2429 eq277)
  have eq2471 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (X0 ◇ (e X1))) ◇ X1))) := by first | exact superpose eq47 eq2428 | exact mod_symm (superpose eq47 eq2428) | exact superpose eq2428 eq47 | exact mod_symm (superpose eq2428 eq47)
  have eq2476 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((v (e X0)) ◇ ((e X1) ◇ ((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0)))))) := by first | exact superpose eq13 eq2410 | exact mod_symm (superpose eq13 eq2410) | exact superpose eq2410 eq13 | exact mod_symm (superpose eq2410 eq13)
  have eq2505 (X0 X1 : G) : (w X1 (e X0)) = (e (v (X0 ◇ ((e X0) ◇ (X1 ◇ X1))))) := by first | exact superpose eq949 eq2470 | exact mod_symm (superpose eq949 eq2470) | exact superpose eq2470 eq949 | exact mod_symm (superpose eq2470 eq949)
  have eq2506 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (e X1)) ◇ (X0 ◇ X1)))) := by first | exact superpose eq2466 eq2471 | exact mod_symm (superpose eq2466 eq2471) | exact superpose eq2471 eq2466 | exact mod_symm (superpose eq2471 eq2466)
  have eq2510 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((((v (e X0)) ◇ (v (e X0))) ◇ (e X1)) ◇ (v ((e X0) ◇ (e X0)))) := by first | exact superpose eq739 eq2476 | exact mod_symm (superpose eq739 eq2476) | exact superpose eq2476 eq739 | exact mod_symm (superpose eq2476 eq739)
  have eq2530 (X0 X1 : G) : (w X1 (e X0)) = (e (v (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq276 eq2505 | exact mod_symm (superpose eq276 eq2505) | exact superpose eq2505 eq276 | exact mod_symm (superpose eq2505 eq276)
  have eq2531 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by first | exact superpose eq396 eq2506 | exact mod_symm (superpose eq396 eq2506) | exact superpose eq2506 eq396 | exact mod_symm (superpose eq2506 eq396)
  have eq2535 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((v (e X0)) ◇ ((e X1) ◇ ((v (e X0)) ◇ (v ((e X0) ◇ (e X0)))))) := by first | exact superpose eq1242 eq2510 | exact mod_symm (superpose eq1242 eq2510) | exact superpose eq2510 eq1242 | exact mod_symm (superpose eq2510 eq1242)
  have eq2552 (X0 X1 : G) : (w X0 (e X1)) = (e (v (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by first | exact superpose eq2466 eq2531 | exact mod_symm (superpose eq2466 eq2531) | exact superpose eq2531 eq2466 | exact mod_symm (superpose eq2531 eq2466)
  have eq2554 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (((e X1) ◇ (v (e X0))) ◇ (v ((e X0) ◇ ((e X0) ◇ (e X0))))) := by first | exact superpose eq416 eq2535 | exact mod_symm (superpose eq416 eq2535) | exact superpose eq2535 eq416 | exact mod_symm (superpose eq2535 eq416)
  have eq2566 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (v (((e X0) ◇ ((e X0) ◇ (e X0))) ◇ (e X0)))) := by first | exact superpose eq621 eq2554 | exact mod_symm (superpose eq621 eq2554) | exact superpose eq2554 eq621 | exact mod_symm (superpose eq2554 eq621)
  have eq2578 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (v (((e X0) ◇ (e X0)) ◇ ((e X0) ◇ (e X0))))) := by first | exact superpose eq2391 eq2566 | exact mod_symm (superpose eq2391 eq2566) | exact superpose eq2566 eq2391 | exact mod_symm (superpose eq2566 eq2391)
  have eq2585 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (v ((e X0) ◇ (((e X0) ◇ (e X0)) ◇ (e X0))))) := by first | exact superpose eq444 eq2578 | exact mod_symm (superpose eq444 eq2578) | exact superpose eq2578 eq444 | exact mod_symm (superpose eq2578 eq444)
  have eq2588 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (v ((e X0) ◇ ((e X0) ◇ ((e X0) ◇ (e X0)))))) := by first | exact superpose eq444 eq2585 | exact mod_symm (superpose eq444 eq2585) | exact superpose eq2585 eq444 | exact mod_symm (superpose eq2585 eq444)
  have eq2589 (X0 X1 : G) : ((e X0) ◇ (e X1)) = ((e X1) ◇ (e X0)) := by first | exact superpose eq19 eq2588 | exact mod_symm (superpose eq19 eq2588) | exact superpose eq2588 eq19 | exact mod_symm (superpose eq2588 eq19)
  have eq2590 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq2589 | exact mod_symm (superpose eq14 eq2589) | exact superpose eq2589 eq14 | exact mod_symm (superpose eq2589 eq14)
  have eq2606 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((e (X0 ◇ (e X0))) ◇ X1) ◇ X1))) := by first | exact superpose eq28 eq52 | exact mod_symm (superpose eq28 eq52) | exact superpose eq52 eq28 | exact mod_symm (superpose eq52 eq28)
  have eq2610 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e ((X0 ◇ X0) ◇ X1)) ◇ (e X1)))) := by first | exact superpose eq14 eq52 | exact mod_symm (superpose eq14 eq52) | exact superpose eq52 eq14 | exact mod_symm (superpose eq52 eq14)
  have eq2634 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (((e (X0 ◇ X0)) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq52 eq47 | exact mod_symm (superpose eq52 eq47) | exact superpose eq47 eq52 | exact mod_symm (superpose eq47 eq52)
  have eq2661 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq395 eq2634 | exact mod_symm (superpose eq395 eq2634) | exact superpose eq2634 eq395 | exact mod_symm (superpose eq2634 eq395)
  have eq2684 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e ((X0 ◇ X0) ◇ X1)) ◇ X1))) := by first | exact superpose eq47 eq2610 | exact mod_symm (superpose eq47 eq2610) | exact superpose eq2610 eq47 | exact mod_symm (superpose eq2610 eq47)
  have eq2688 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((X0 ◇ (e X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq395 eq2606 | exact mod_symm (superpose eq395 eq2606) | exact superpose eq2606 eq395 | exact mod_symm (superpose eq2606 eq395)
  have eq2708 (X0 X1 : G) : (w X0 (e X1)) = (w (e X0) (e X1)) := by first | exact superpose eq254 eq2661 | exact mod_symm (superpose eq254 eq2661) | exact superpose eq2661 eq254 | exact mod_symm (superpose eq2661 eq254)
  have eq2731 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq105 eq2684 | exact mod_symm (superpose eq105 eq2684) | exact superpose eq2684 eq105 | exact mod_symm (superpose eq2684 eq105)
  have eq2735 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e (e X0)) X1) := by first | exact superpose eq1889 eq2688 | exact mod_symm (superpose eq1889 eq2688) | exact superpose eq2688 eq1889 | exact mod_symm (superpose eq2688 eq1889)
  have eq2771 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w X0 (e X1)) := by first | exact superpose eq2708 eq2731 | exact mod_symm (superpose eq2708 eq2731) | exact superpose eq2731 eq2708 | exact mod_symm (superpose eq2731 eq2708)
  have eq2775 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e X0) X1) := by first | exact superpose eq16 eq2735 | exact mod_symm (superpose eq16 eq2735) | exact superpose eq2735 eq16 | exact mod_symm (superpose eq2735 eq16)
  have eq2797 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq20 eq2771 | exact mod_symm (superpose eq20 eq2771) | exact superpose eq2771 eq20 | exact mod_symm (superpose eq2771 eq20)
  have eq2801 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq20 eq2775 | exact mod_symm (superpose eq20 eq2775) | exact superpose eq2775 eq20 | exact mod_symm (superpose eq2775 eq20)
  have eq3978 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e (X0 ◇ (X1 ◇ X1))) ◇ (e X0)))) := by first | exact superpose eq2590 eq52 | exact mod_symm (superpose eq2590 eq52) | exact superpose eq52 eq2590 | exact mod_symm (superpose eq52 eq2590)
  have eq3991 (X0 : G) : (e (e X0)) = (e (v ((e X0) ◇ ((e X0) ◇ (e (X0 ◇ X0)))))) := by first | exact superpose eq2590 eq89 | exact mod_symm (superpose eq2590 eq89) | exact superpose eq89 eq2590 | exact mod_symm (superpose eq89 eq2590)
  have eq4022 (X0 : G) : (e (e X0)) = (e (v ((e X0) ◇ ((e X0) ◇ (X0 ◇ X0))))) := by first | exact superpose eq277 eq3991 | exact mod_symm (superpose eq277 eq3991) | exact superpose eq3991 eq277 | exact mod_symm (superpose eq3991 eq277)
  have eq4033 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e (X0 ◇ (X1 ◇ X1))) ◇ X0))) := by first | exact superpose eq47 eq3978 | exact mod_symm (superpose eq47 eq3978) | exact superpose eq3978 eq47 | exact mod_symm (superpose eq3978 eq47)
  have eq4069 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ ((X0 ◇ (e X0)) ◇ (e X0))))) := by first | exact superpose eq758 eq4022 | exact mod_symm (superpose eq758 eq4022) | exact superpose eq4022 eq758 | exact mod_symm (superpose eq4022 eq758)
  have eq4080 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by first | exact superpose eq105 eq4033 | exact mod_symm (superpose eq105 eq4033) | exact superpose eq4033 eq105 | exact mod_symm (superpose eq4033 eq105)
  have eq4097 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ ((X0 ◇ (e X0)) ◇ X0)))) := by first | exact superpose eq277 eq4069 | exact mod_symm (superpose eq277 eq4069) | exact superpose eq4069 eq277 | exact mod_symm (superpose eq4069 eq277)
  have eq4105 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := by first | exact superpose eq2466 eq4080 | exact mod_symm (superpose eq2466 eq4080) | exact superpose eq4080 eq2466 | exact mod_symm (superpose eq4080 eq2466)
  have eq4114 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ (e X0)))))) := by first | exact superpose eq949 eq4097 | exact mod_symm (superpose eq949 eq4097) | exact superpose eq4097 eq949 | exact mod_symm (superpose eq4097 eq949)
  have eq4118 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by first | exact superpose eq2466 eq4105 | exact mod_symm (superpose eq2466 eq4105) | exact superpose eq4105 eq2466 | exact mod_symm (superpose eq4105 eq2466)
  have eq4121 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq1152 eq4114 | exact mod_symm (superpose eq1152 eq4114) | exact superpose eq4114 eq1152 | exact mod_symm (superpose eq4114 eq1152)
  have eq4125 (X0 X1 : G) : (w X0 (e X1)) = (w (e X1) (e X0)) := by first | exact superpose eq2530 eq4118 | exact mod_symm (superpose eq2530 eq4118) | exact superpose eq4118 eq2530 | exact mod_symm (superpose eq4118 eq2530)
  have eq4126 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by first | exact superpose eq949 eq4121 | exact mod_symm (superpose eq949 eq4121) | exact superpose eq4121 eq949 | exact mod_symm (superpose eq4121 eq949)
  have eq4127 (X0 X1 : G) : (w X0 (e X1)) = (w (e X1) X0) := by first | exact superpose eq2797 eq4125 | exact mod_symm (superpose eq2797 eq4125) | exact superpose eq4125 eq2797 | exact mod_symm (superpose eq4125 eq2797)
  have eq4128 (X0 : G) : (e (e X0)) = (w X0 (e X0)) := by first | exact superpose eq2552 eq4126 | exact mod_symm (superpose eq2552 eq4126) | exact superpose eq4126 eq2552 | exact mod_symm (superpose eq4126 eq2552)
  have eq4129 (X0 X1 : G) : (w X0 (e X1)) = (w X1 X0) := by first | exact superpose eq2801 eq4127 | exact mod_symm (superpose eq2801 eq4127) | exact superpose eq4127 eq2801 | exact mod_symm (superpose eq4127 eq2801)
  have eq4130 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq2797 eq4128 | exact mod_symm (superpose eq2797 eq4128) | exact superpose eq4128 eq2797 | exact mod_symm (superpose eq4128 eq2797)
  have eq4131 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq16 eq4130 | exact mod_symm (superpose eq16 eq4130) | exact superpose eq4130 eq16 | exact mod_symm (superpose eq4130 eq16)
  have eq4466 : (w x (w y y)) ≠ (w y (e x)) := by first | exact superpose eq4131 eq21 | exact mod_symm (superpose eq4131 eq21) | exact superpose eq21 eq4131 | exact mod_symm (superpose eq21 eq4131)
  have eq4467 : (w x (w y y)) ≠ (w y x) := by first | exact superpose eq2797 eq4466 | exact mod_symm (superpose eq2797 eq4466) | exact superpose eq4466 eq2797 | exact mod_symm (superpose eq4466 eq2797)
  have eq4480 : (w y x) ≠ (w x (e y)) := by first | exact superpose eq4131 eq4467 | exact mod_symm (superpose eq4131 eq4467) | exact superpose eq4467 eq4131 | exact mod_symm (superpose eq4467 eq4131)
  subsumption eq4480 eq4129


/-- Equation 4541 `x ◇ (y ◇ z) = (z ◇ x) ◇ y` is term-definable from equation 4364 over finite magmas, via the term
`x □ y := u^[1N+1] (x ◇ y)` with `u a = (a ◇ (a ◇ a))`. -/
private theorem aux4364_4541 [Magma G] (h : Equation4364 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, ((v (e a)) ◇ ((v (e a)) ◇ (v (e a)))) = e a)
    (hvue : ∀ a : G, v ((e a) ◇ ((e a) ◇ (e a))) = e a)
    (hw : ∀ a b : G, w a b = (e ((a ◇ b))))
    (x y z : G) :
    (w x (w y z)) =
      (w (w z x) y) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ ((v (e X0)) ◇ (v (e X0)))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ ((e X0) ◇ (e X0)))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (e (X0 ◇ X1)) = (w X0 X1) := mod_symm (hw ..)
  have eq21 : (w x (w y z)) ≠ (w (w z x) y) := mod_symm nh
  have eq22 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (w X0 X1) := by first | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14) | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20)
  have eq26 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq27 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq30 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (w (e X0) X1) := by first | exact superpose eq16 eq22 | exact mod_symm (superpose eq16 eq22) | exact superpose eq22 eq16 | exact mod_symm (superpose eq22 eq16)
  have eq31 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = ((w X0 X1) ◇ (e X2)) := by first | exact superpose eq20 eq22 | exact mod_symm (superpose eq20 eq22) | exact superpose eq22 eq20 | exact mod_symm (superpose eq22 eq20)
  have eq33 (X0 X1 : G) : (w X1 (e X0)) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq22 | exact mod_symm (superpose eq16 eq22) | exact superpose eq22 eq16 | exact mod_symm (superpose eq22 eq16)
  have eq34 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = ((e X2) ◇ (w X0 X1)) := by first | exact superpose eq20 eq22 | exact mod_symm (superpose eq20 eq22) | exact superpose eq22 eq20 | exact mod_symm (superpose eq22 eq20)
  have eq35 (X0 X1 X2 : G) : ((e X2) ◇ (w X0 X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq27 eq22 | exact mod_symm (superpose eq27 eq22) | exact superpose eq22 eq27 | exact mod_symm (superpose eq22 eq27)
  have eq38 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq22 eq33 | exact mod_symm (superpose eq22 eq33) | exact superpose eq33 eq22 | exact mod_symm (superpose eq33 eq22)
  have eq39 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq22 eq30 | exact mod_symm (superpose eq22 eq30) | exact superpose eq30 eq22 | exact mod_symm (superpose eq30 eq22)
  have eq40 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq20 eq38 | exact mod_symm (superpose eq20 eq38) | exact superpose eq38 eq20 | exact mod_symm (superpose eq38 eq20)
  have eq46 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = (w (w X0 X1) X2) := by first | exact superpose eq20 eq39 | exact mod_symm (superpose eq20 eq39) | exact superpose eq39 eq20 | exact mod_symm (superpose eq39 eq20)
  have eq53 (X0 X1 X2 : G) : ((v X0) ◇ ((v X1) ◇ X2)) = (X2 ◇ (v (X0 ◇ X1))) := by first | exact superpose eq15 eq13 | exact mod_symm (superpose eq15 eq13) | exact superpose eq13 eq15 | exact mod_symm (superpose eq13 eq15)
  have eq54 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq55 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq58 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ (X2 ◇ (v X0))) := by first | exact superpose eq15 eq13 | exact mod_symm (superpose eq15 eq13) | exact superpose eq13 eq15 | exact mod_symm (superpose eq13 eq15)
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq63 (X0 X1 X2 : G) : (e (X0 ◇ (X1 ◇ X2))) = (w X1 (X2 ◇ X0)) := by first | exact superpose eq13 eq20 | exact mod_symm (superpose eq13 eq20) | exact superpose eq20 eq13 | exact mod_symm (superpose eq20 eq13)
  have eq64 (X0 X1 X2 : G) : (w X0 (X1 ◇ X2)) = (w X1 (X2 ◇ X0)) := by first | exact superpose eq20 eq63 | exact mod_symm (superpose eq20 eq63) | exact superpose eq63 eq20 | exact mod_symm (superpose eq63 eq20)
  have eq82 (X0 : G) : (e X0) = (v ((e X0) ◇ (w X0 X0))) := by first | exact superpose eq22 eq19 | exact mod_symm (superpose eq22 eq19) | exact superpose eq19 eq22 | exact mod_symm (superpose eq19 eq22)
  have eq87 (X0 : G) : (e X0) = (v (w X0 (w X0 X0))) := by first | exact superpose eq35 eq82 | exact mod_symm (superpose eq35 eq82) | exact superpose eq82 eq35 | exact mod_symm (superpose eq82 eq35)
  have eq90 (X0 : G) : (e X0) = (v (w X0 (X0 ◇ X0))) := by first | exact superpose eq40 eq87 | exact mod_symm (superpose eq40 eq87) | exact superpose eq87 eq40 | exact mod_symm (superpose eq87 eq40)
  have eq211 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w (e X0) ((e X1) ◇ X2)) := by first | exact superpose eq22 eq64 | exact mod_symm (superpose eq22 eq64) | exact superpose eq64 eq22 | exact mod_symm (superpose eq64 eq22)
  have eq214 (X0 X1 X2 X3 : G) : (w X1 ((X2 ◇ X0) ◇ X3)) = (w X3 (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq13 eq64 | exact mod_symm (superpose eq13 eq64) | exact superpose eq64 eq13 | exact mod_symm (superpose eq64 eq13)
  have eq218 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w (e X1) (X2 ◇ (e X0))) := by first | exact superpose eq22 eq64 | exact mod_symm (superpose eq22 eq64) | exact superpose eq64 eq22 | exact mod_symm (superpose eq64 eq22)
  have eq221 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ X2))) = (w (X2 ◇ X0) (X3 ◇ X1)) := by first | exact superpose eq13 eq64 | exact mod_symm (superpose eq13 eq64) | exact superpose eq64 eq13 | exact mod_symm (superpose eq64 eq13)
  have eq227 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X0 (X1 ◇ (e X2))) := by first | exact superpose eq64 eq39 | exact mod_symm (superpose eq64 eq39) | exact superpose eq39 eq64 | exact mod_symm (superpose eq39 eq64)
  have eq230 (X0 X1 X2 : G) : (w X1 (X2 ◇ X0)) = (w X0 ((e X1) ◇ X2)) := by first | exact superpose eq64 eq39 | exact mod_symm (superpose eq64 eq39) | exact superpose eq39 eq64 | exact mod_symm (superpose eq39 eq64)
  have eq232 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w X1 (X2 ◇ (e X0))) := by first | exact superpose eq39 eq218 | exact mod_symm (superpose eq39 eq218) | exact superpose eq218 eq39 | exact mod_symm (superpose eq218 eq39)
  have eq234 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w X0 ((e X1) ◇ X2)) := by first | exact superpose eq39 eq211 | exact mod_symm (superpose eq39 eq211) | exact superpose eq211 eq39 | exact mod_symm (superpose eq211 eq39)
  have eq236 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X1 (X2 ◇ (e X0))) := by first | exact superpose eq40 eq232 | exact mod_symm (superpose eq40 eq232) | exact superpose eq232 eq40 | exact mod_symm (superpose eq232 eq40)
  have eq238 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X0 ((e X1) ◇ X2)) := by first | exact superpose eq40 eq234 | exact mod_symm (superpose eq40 eq234) | exact superpose eq234 eq40 | exact mod_symm (superpose eq234 eq40)
  have eq268 (X0 X1 X2 X3 : G) : (w (X2 ◇ X3) (X0 ◇ X1)) = ((w X2 X3) ◇ (w X0 X1)) := by first | exact superpose eq20 eq31 | exact mod_symm (superpose eq20 eq31) | exact superpose eq31 eq20 | exact mod_symm (superpose eq31 eq20)
  have eq315 : (w x (w y z)) ≠ (w (z ◇ x) y) := by first | exact superpose eq46 eq21 | exact mod_symm (superpose eq46 eq21) | exact superpose eq21 eq46 | exact mod_symm (superpose eq21 eq46)
  have eq317 (X0 X1 X2 X3 : G) : (w X3 (w (X0 ◇ X1) X2)) = (w X3 ((w X0 X1) ◇ X2)) := by first | exact superpose eq46 eq40 | exact mod_symm (superpose eq46 eq40) | exact superpose eq40 eq46 | exact mod_symm (superpose eq40 eq46)
  have eq321 (X0 X1 X2 X3 : G) : (w (X0 ◇ X1) (X2 ◇ X3)) = (w X3 ((w X0 X1) ◇ X2)) := by first | exact superpose eq46 eq64 | exact mod_symm (superpose eq46 eq64) | exact superpose eq64 eq46 | exact mod_symm (superpose eq64 eq46)
  have eq328 (X0 X1 X2 X3 : G) : ((w X0 X1) ◇ (w X2 X3)) = (w X3 ((w X0 X1) ◇ X2)) := by first | exact superpose eq268 eq321 | exact mod_symm (superpose eq268 eq321) | exact superpose eq321 eq268 | exact mod_symm (superpose eq321 eq268)
  have eq330 (X0 X1 X2 X3 : G) : (w X3 ((X0 ◇ X1) ◇ X2)) = (w X3 ((w X0 X1) ◇ X2)) := by first | exact superpose eq40 eq317 | exact mod_symm (superpose eq40 eq317) | exact superpose eq317 eq40 | exact mod_symm (superpose eq317 eq40)
  have eq332 : (w (z ◇ x) y) ≠ (w x (y ◇ z)) := by first | exact superpose eq40 eq315 | exact mod_symm (superpose eq40 eq315) | exact superpose eq315 eq40 | exact mod_symm (superpose eq315 eq40)
  have eq346 (X0 X1 X2 X3 : G) : (w X3 ((X0 ◇ X1) ◇ X2)) = ((w X0 X1) ◇ (w X2 X3)) := by first | exact superpose eq328 eq330 | exact mod_symm (superpose eq328 eq330) | exact superpose eq330 eq328 | exact mod_symm (superpose eq330 eq328)
  have eq354 (X0 X1 X2 X3 : G) : (w (v (X0 ◇ X1)) (X2 ◇ X3)) = ((v (w X0 X1)) ◇ (w X2 X3)) := by first | exact superpose eq26 eq34 | exact mod_symm (superpose eq26 eq34) | exact superpose eq34 eq26 | exact mod_symm (superpose eq34 eq26)
  have eq366 (X0 X1 X2 X3 : G) : (w X3 (w X0 (X1 ◇ X2))) = (w (e X0) ((w X1 X2) ◇ X3)) := by first | exact superpose eq34 eq64 | exact mod_symm (superpose eq34 eq64) | exact superpose eq64 eq34 | exact mod_symm (superpose eq64 eq34)
  have eq373 (X0 X1 X2 X3 : G) : (w X3 (w X0 (X1 ◇ X2))) = (w X0 ((w X1 X2) ◇ X3)) := by first | exact superpose eq39 eq366 | exact mod_symm (superpose eq39 eq366) | exact superpose eq366 eq39 | exact mod_symm (superpose eq366 eq39)
  have eq388 (X0 X1 X2 X3 : G) : (w X3 (w X0 (X1 ◇ X2))) = ((w X1 X2) ◇ (w X3 X0)) := by first | exact superpose eq328 eq373 | exact mod_symm (superpose eq328 eq373) | exact superpose eq373 eq328 | exact mod_symm (superpose eq373 eq328)
  have eq395 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ X2))) = ((w X1 X2) ◇ (w X3 X0)) := by first | exact superpose eq40 eq388 | exact mod_symm (superpose eq40 eq388) | exact superpose eq388 eq40 | exact mod_symm (superpose eq388 eq40)
  have eq683 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = ((v X3) ◇ (X0 ◇ (X1 ◇ (v X2)))) := by first | exact superpose eq13 eq53 | exact mod_symm (superpose eq13 eq53) | exact superpose eq53 eq13 | exact mod_symm (superpose eq53 eq13)
  have eq832 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (v (X1 ◇ X2)))) = (w (X0 ◇ (v X1)) (X3 ◇ (v X2))) := by first | exact superpose eq58 eq64 | exact mod_symm (superpose eq58 eq64) | exact superpose eq64 eq58 | exact mod_symm (superpose eq64 eq58)
  have eq835 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (v (X1 ◇ X2)))) = ((w X0 (v X1)) ◇ (w X3 (v X2))) := by first | exact superpose eq268 eq832 | exact mod_symm (superpose eq268 eq832) | exact superpose eq832 eq268 | exact mod_symm (superpose eq832 eq268)
  have eq997 (X0 X1 X2 X3 : G) : (w (v (X0 ◇ X1)) (X2 ◇ X3)) = (w X3 ((v (w X0 X1)) ◇ X2)) := by first | exact superpose eq26 eq230 | exact mod_symm (superpose eq26 eq230) | exact superpose eq230 eq26 | exact mod_symm (superpose eq230 eq26)
  have eq1050 (X0 X1 X2 X3 : G) : ((v (w X0 X1)) ◇ (w X2 X3)) = (w X3 ((v (w X0 X1)) ◇ X2)) := by first | exact superpose eq354 eq997 | exact mod_symm (superpose eq354 eq997) | exact superpose eq997 eq354 | exact mod_symm (superpose eq997 eq354)
  have eq1166 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w (e X0) (X1 ◇ X2)) := by first | exact superpose eq22 eq236 | exact mod_symm (superpose eq22 eq236) | exact superpose eq236 eq22 | exact mod_symm (superpose eq236 eq22)
  have eq1211 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w X0 (X1 ◇ X2)) := by first | exact superpose eq39 eq1166 | exact mod_symm (superpose eq39 eq1166) | exact superpose eq1166 eq39 | exact mod_symm (superpose eq1166 eq39)
  have eq1305 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X1) ◇ X0) ◇ (v (X4 ◇ X2))) = ((v X4) ◇ (X0 ◇ (X1 ◇ ((v X2) ◇ X3)))) := by first | exact superpose eq54 eq53 | exact mod_symm (superpose eq54 eq53) | exact superpose eq53 eq54 | exact mod_symm (superpose eq53 eq54)
  have eq1307 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by first | exact superpose eq54 eq13 | exact mod_symm (superpose eq54 eq13) | exact superpose eq13 eq54 | exact mod_symm (superpose eq13 eq54)
  have eq1506 (X0 X1 X2 : G) : (w X0 (w X1 X2)) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq1211 eq64 | exact mod_symm (superpose eq1211 eq64) | exact superpose eq64 eq1211 | exact mod_symm (superpose eq64 eq1211)
  have eq1643 (X0 X1 X2 X3 X4 : G) : (((v X2) ◇ X0) ◇ ((X4 ◇ (v X1)) ◇ X3)) = (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq53 eq55 | exact mod_symm (superpose eq53 eq55) | exact superpose eq55 eq53 | exact mod_symm (superpose eq55 eq53)
  have eq1810 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = ((v X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ (v X1)))) := by first | exact superpose eq1307 eq1643 | exact mod_symm (superpose eq1307 eq1643) | exact superpose eq1643 eq1307 | exact mod_symm (superpose eq1643 eq1307)
  have eq1855 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = (((X0 ◇ X3) ◇ X4) ◇ (v (X2 ◇ X1))) := by first | exact superpose eq683 eq1810 | exact mod_symm (superpose eq683 eq1810) | exact superpose eq1810 eq683 | exact mod_symm (superpose eq1810 eq683)
  have eq2876 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = ((v (e X0)) ◇ (X1 ◇ (X2 ◇ ((v (e X0)) ◇ (v (e X0)))))) := by first | exact superpose eq18 eq60 | exact mod_symm (superpose eq18 eq60) | exact superpose eq60 eq18 | exact mod_symm (superpose eq60 eq18)
  have eq3032 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = ((((v (e X0)) ◇ X2) ◇ X1) ◇ (v ((e X0) ◇ (e X0)))) := by first | exact superpose eq1305 eq2876 | exact mod_symm (superpose eq1305 eq2876) | exact superpose eq2876 eq1305 | exact mod_symm (superpose eq2876 eq1305)
  have eq3148 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((v (e X0)) ◇ (v ((e X0) ◇ (e X0)))))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1855 eq3032 | exact mod_symm (superpose eq1855 eq3032) | exact superpose eq3032 eq1855 | exact mod_symm (superpose eq3032 eq1855)
  have eq3212 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (v ((e X0) ◇ ((e X0) ◇ (e X0)))))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq15 eq3148 | exact mod_symm (superpose eq15 eq3148) | exact superpose eq3148 eq15 | exact mod_symm (superpose eq3148 eq15)
  have eq3240 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq19 eq3212 | exact mod_symm (superpose eq19 eq3212) | exact superpose eq3212 eq19 | exact mod_symm (superpose eq3212 eq19)
  have eq3268 (X0 X1 X2 X3 : G) : (w X3 ((v (w X0 X1)) ◇ X2)) = (w X2 (X3 ◇ (v (X0 ◇ X1)))) := by first | exact superpose eq26 eq238 | exact mod_symm (superpose eq26 eq238) | exact superpose eq238 eq26 | exact mod_symm (superpose eq238 eq26)
  have eq3358 (X0 X1 X2 X3 : G) : ((v (w X0 X1)) ◇ (w X2 X3)) = (w X2 (X3 ◇ (v (X0 ◇ X1)))) := by first | exact superpose eq1050 eq3268 | exact mod_symm (superpose eq1050 eq3268) | exact superpose eq3268 eq1050 | exact mod_symm (superpose eq3268 eq1050)
  have eq8025 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ (e X2)))) = (w X2 (X3 ◇ (X1 ◇ X0))) := by first | exact superpose eq3240 eq227 | exact mod_symm (superpose eq3240 eq227) | exact superpose eq227 eq3240 | exact mod_symm (superpose eq227 eq3240)
  have eq8029 (X0 X1 X2 : G) : (w (X1 ◇ X0) (e X2)) = (e (X0 ◇ (X1 ◇ (e X2)))) := by first | exact superpose eq3240 eq20 | exact mod_symm (superpose eq3240 eq20) | exact superpose eq20 eq3240 | exact mod_symm (superpose eq20 eq3240)
  have eq8067 (X0 X1 X2 : G) : (w X0 (X1 ◇ (e X2))) = (w (X1 ◇ X0) (e X2)) := by first | exact superpose eq20 eq8029 | exact mod_symm (superpose eq20 eq8029) | exact superpose eq8029 eq20 | exact mod_symm (superpose eq8029 eq20)
  have eq8069 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ (e X2)))) = ((w X1 X0) ◇ (w X2 X3)) := by first | exact superpose eq395 eq8025 | exact mod_symm (superpose eq395 eq8025) | exact superpose eq8025 eq395 | exact mod_symm (superpose eq8025 eq395)
  have eq8114 (X0 X1 X2 : G) : (w X0 (X1 ◇ (e X2))) = (w (X1 ◇ X0) X2) := by first | exact superpose eq38 eq8067 | exact mod_symm (superpose eq38 eq8067) | exact superpose eq8067 eq38 | exact mod_symm (superpose eq8067 eq38)
  have eq8116 (X0 X1 X2 X3 : G) : ((w X1 (e X2)) ◇ (w X3 X0)) = ((w X1 X0) ◇ (w X2 X3)) := by first | exact superpose eq395 eq8069 | exact mod_symm (superpose eq395 eq8069) | exact superpose eq8069 eq395 | exact mod_symm (superpose eq8069 eq395)
  have eq8152 (X0 X1 X2 : G) : (w X1 (X2 ◇ X0)) = (w (X1 ◇ X0) X2) := by first | exact superpose eq236 eq8114 | exact mod_symm (superpose eq236 eq8114) | exact superpose eq8114 eq236 | exact mod_symm (superpose eq8114 eq236)
  have eq8153 (X0 X1 X2 X3 : G) : ((w X1 X2) ◇ (w X3 X0)) = ((w X1 X0) ◇ (w X2 X3)) := by first | exact superpose eq38 eq8116 | exact mod_symm (superpose eq38 eq8116) | exact superpose eq8116 eq38 | exact mod_symm (superpose eq8116 eq38)
  have eq11665 (X0 X1 X2 X3 X4 : G) : (w X3 ((X0 ◇ (v (X1 ◇ X2))) ◇ X4)) = (w X4 ((X0 ◇ (v X1)) ◇ (X3 ◇ (v X2)))) := by first | exact superpose eq58 eq214 | exact mod_symm (superpose eq58 eq214) | exact superpose eq214 eq58 | exact mod_symm (superpose eq214 eq58)
  have eq11673 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ (e X2)))) = (w (e X2) (X0 ◇ (X3 ◇ X1))) := by first | exact superpose eq3240 eq214 | exact mod_symm (superpose eq3240 eq214) | exact superpose eq214 eq3240 | exact mod_symm (superpose eq214 eq3240)
  have eq12052 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ (e X2)))) = (w X2 (X0 ◇ (X3 ◇ X1))) := by first | exact superpose eq39 eq11673 | exact mod_symm (superpose eq39 eq11673) | exact superpose eq11673 eq39 | exact mod_symm (superpose eq11673 eq39)
  have eq12060 (X0 X1 X2 X3 X4 : G) : (w X3 ((X0 ◇ (v (X1 ◇ X2))) ◇ X4)) = ((w X3 (v X2)) ◇ (w X4 (X0 ◇ (v X1)))) := by first | exact superpose eq395 eq11665 | exact mod_symm (superpose eq395 eq11665) | exact superpose eq11665 eq395 | exact mod_symm (superpose eq11665 eq395)
  have eq12237 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ (e X2)))) = ((w X3 X1) ◇ (w X2 X0)) := by first | exact superpose eq395 eq12052 | exact mod_symm (superpose eq395 eq12052) | exact superpose eq12052 eq395 | exact mod_symm (superpose eq12052 eq395)
  have eq12245 (X0 X1 X2 X3 X4 : G) : ((w X0 (v (X1 ◇ X2))) ◇ (w X4 X3)) = ((w X3 (v X2)) ◇ (w X4 (X0 ◇ (v X1)))) := by first | exact superpose eq346 eq12060 | exact mod_symm (superpose eq346 eq12060) | exact superpose eq12060 eq346 | exact mod_symm (superpose eq12060 eq346)
  have eq12386 (X0 X1 X2 X3 : G) : ((w X1 (e X2)) ◇ (w X3 X0)) = ((w X3 X1) ◇ (w X2 X0)) := by first | exact superpose eq395 eq12237 | exact mod_symm (superpose eq395 eq12237) | exact superpose eq12237 eq395 | exact mod_symm (superpose eq12237 eq395)
  have eq12509 (X0 X1 X2 X3 : G) : ((w X1 X2) ◇ (w X3 X0)) = ((w X3 X1) ◇ (w X2 X0)) := by first | exact superpose eq38 eq12386 | exact mod_symm (superpose eq38 eq12386) | exact superpose eq12386 eq38 | exact mod_symm (superpose eq12386 eq38)
  have eq15608 (X0 X1 X2 : G) : (w (v (e X0)) (X1 ◇ (((v (e X0)) ◇ (v (e X0))) ◇ X2))) = (w (X2 ◇ X1) (e X0)) := by first | exact superpose eq18 eq221 | exact mod_symm (superpose eq18 eq221) | exact superpose eq221 eq18 | exact mod_symm (superpose eq221 eq18)
  have eq15880 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = (w (v (e X0)) (X1 ◇ (((v (e X0)) ◇ (v (e X0))) ◇ X2))) := by first | exact superpose eq38 eq15608 | exact mod_symm (superpose eq38 eq15608) | exact superpose eq15608 eq38 | exact mod_symm (superpose eq15608 eq38)
  have eq16109 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = ((w ((v (e X0)) ◇ (v (e X0))) X2) ◇ (w (v (e X0)) X1)) := by first | exact superpose eq395 eq15880 | exact mod_symm (superpose eq395 eq15880) | exact superpose eq15880 eq395 | exact mod_symm (superpose eq15880 eq395)
  have eq16293 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = ((w X2 (v (e X0))) ◇ (w ((v (e X0)) ◇ (v (e X0))) X1)) := by first | exact superpose eq12509 eq16109 | exact mod_symm (superpose eq12509 eq16109) | exact superpose eq16109 eq12509 | exact mod_symm (superpose eq16109 eq12509)
  have eq16436 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = ((w X2 (v (e X0))) ◇ (w (v (e X0)) (X1 ◇ (v (e X0))))) := by first | exact superpose eq8152 eq16293 | exact mod_symm (superpose eq8152 eq16293) | exact superpose eq16293 eq8152 | exact mod_symm (superpose eq16293 eq8152)
  have eq16546 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = ((w X1 (v ((e X0) ◇ (e X0)))) ◇ (w (v (e X0)) X2)) := by first | exact superpose eq12245 eq16436 | exact mod_symm (superpose eq12245 eq16436) | exact superpose eq16436 eq12245 | exact mod_symm (superpose eq16436 eq12245)
  have eq16633 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = ((w X1 (v (e X0))) ◇ (w X2 (v ((e X0) ◇ (e X0))))) := by first | exact superpose eq8153 eq16546 | exact mod_symm (superpose eq8153 eq16546) | exact superpose eq16546 eq8153 | exact mod_symm (superpose eq16546 eq8153)
  have eq16686 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = (w X2 (X1 ◇ (v ((e X0) ◇ ((e X0) ◇ (e X0)))))) := by first | exact superpose eq835 eq16633 | exact mod_symm (superpose eq835 eq16633) | exact superpose eq16633 eq835 | exact mod_symm (superpose eq16633 eq835)
  have eq16717 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = ((v (w (e X0) ((e X0) ◇ (e X0)))) ◇ (w X2 X1)) := by first | exact superpose eq3358 eq16686 | exact mod_symm (superpose eq3358 eq16686) | exact superpose eq16686 eq3358 | exact mod_symm (superpose eq16686 eq3358)
  have eq16739 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = ((e (e X0)) ◇ (w X2 X1)) := by first | exact superpose eq90 eq16717 | exact mod_symm (superpose eq90 eq16717) | exact superpose eq16717 eq90 | exact mod_symm (superpose eq16717 eq90)
  have eq16749 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = (w (e X0) (w X2 X1)) := by first | exact superpose eq35 eq16739 | exact mod_symm (superpose eq35 eq16739) | exact superpose eq16739 eq35 | exact mod_symm (superpose eq16739 eq35)
  have eq16757 (X0 X1 X2 : G) : (w (X2 ◇ X1) X0) = (w X0 (w X2 X1)) := by first | exact superpose eq39 eq16749 | exact mod_symm (superpose eq39 eq16749) | exact superpose eq16749 eq39 | exact mod_symm (superpose eq16749 eq39)
  have eq16923 : (w x (y ◇ z)) ≠ (w y (w z x)) := by first | exact superpose eq16757 eq332 | exact mod_symm (superpose eq16757 eq332) | exact superpose eq332 eq16757 | exact mod_symm (superpose eq332 eq16757)
  subsumption eq16923 eq1506


theorem Equation332_termDefinableFromFin_Equation4364 :
    Law332.TermDefinableFromFin Law4364 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))))
    (fun G ↦ (tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)) (Term.var 1))) 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4364 G := Law4364.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) a ◇ ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) b :=
    fun a b ↦ endo4364_1 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, ((v (e a)) ◇ ((v (e a)) ◇ ((v (e a)) ◇ (v (e a))))) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v ((e a) ◇ ((e a) ◇ ((e a) ◇ (e a)))) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law332.models_iff]
  intro x y
  exact aux4364_332 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation4343_termDefinableFromFin_Equation4364 :
    Law4343.TermDefinableFromFin Law4364 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))))
    (fun G ↦ (tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)) (Term.var 1))) 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4364 G := Law4364.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) a ◇ ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) b :=
    fun a b ↦ endo4364_1 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, ((v (e a)) ◇ ((v (e a)) ◇ ((v (e a)) ◇ (v (e a))))) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v ((e a) ◇ ((e a) ◇ ((e a) ◇ (e a)))) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law4343.models_iff]
  intro x y
  exact aux4364_4343 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation4541_termDefinableFromFin_Equation4364 :
    Law4541.TermDefinableFromFin Law4364 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))))
    (fun G ↦ (tm (Term.var 0) (Term.var 1))) 0 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4364 G := Law4364.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))) a ◇ ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))) b :=
    fun a b ↦ endo4364_0 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, ((v (e a)) ◇ ((v (e a)) ◇ (v (e a)))) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v ((e a) ◇ ((e a) ◇ (e a))) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law4541.models_iff]
  intro x y z
  exact aux4364_4541 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y z

end Law.MagmaLaw
