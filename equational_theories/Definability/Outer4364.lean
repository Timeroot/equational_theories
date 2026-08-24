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
`x □ y := (((x ◇ x) ◇ y) ◇ y)` with `u a = (a ◇ (a ◇ (a ◇ a)))`
taken at u^[2N+1]. -/
private theorem aux4364_332 [Magma G] (h : Equation4364 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huh : ∀ a b : G, ((a ◇ b) ◇ ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ b)))) = (a ◇ (a ◇ (a ◇ a))) ◇ (b ◇ (b ◇ (b ◇ b))))
    (huv : ∀ a : G, ((v a) ◇ ((v a) ◇ ((v a) ◇ (v a)))) = e a)
    (hvu : ∀ a : G, v (a ◇ (a ◇ (a ◇ a))) = e a)
    (hw : ∀ a b : G, w a b = (e (v ((((a ◇ a) ◇ b) ◇ b)))))
    (x y : G) :
    (w x y) =
      (w y (w x x)) := by
  by_contra nh
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have eq16 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq17 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq18 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq19 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq20 (X0 : G) : (e X0) = ((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) := mod_symm (huv ..)
  have eq21 (X0 : G) : (e X0) = (v (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := mod_symm (hvu ..)
  have eq22 (X0 X1 : G) : (w X0 X1) = (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) := mod_symm (hw ..)
  have eq23 : (w x y) ≠ (w y (w x x)) := mod_symm nh
  have eq27 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq18 eq16 | exact mod_symm (superpose eq18 eq16) | exact superpose eq16 eq18 | exact mod_symm (superpose eq16 eq18)
  have eq28 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq18 eq16 | exact mod_symm (superpose eq18 eq16) | exact superpose eq16 eq18 | exact mod_symm (superpose eq16 eq18)
  have eq29 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq16 eq28 | exact mod_symm (superpose eq16 eq28) | exact superpose eq28 eq16 | exact mod_symm (superpose eq28 eq16)
  have eq30 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq27 | exact mod_symm (superpose eq16 eq27) | exact superpose eq27 eq16 | exact mod_symm (superpose eq27 eq16)
  have eq31 (X0 X1 : G) : (v ((e X0) ◇ X1)) = ((e (v X0)) ◇ (v X1)) := by first | exact superpose eq19 eq17 | exact mod_symm (superpose eq19 eq17) | exact superpose eq17 eq19 | exact mod_symm (superpose eq17 eq19)
  have eq32 (X0 X1 : G) : (v (X1 ◇ (e X0))) = ((v X1) ◇ (e (v X0))) := by first | exact superpose eq19 eq17 | exact mod_symm (superpose eq19 eq17) | exact superpose eq17 eq19 | exact mod_symm (superpose eq17 eq19)
  have eq33 (X0 X1 X2 : G) : ((e X0) ◇ ((e X1) ◇ X2)) = (X2 ◇ (e (X0 ◇ X1))) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq34 (X0 X1 X2 : G) : ((v X0) ◇ ((v X1) ◇ X2)) = (X2 ◇ (v (X0 ◇ X1))) := by first | exact superpose eq17 eq14 | exact mod_symm (superpose eq17 eq14) | exact superpose eq14 eq17 | exact mod_symm (superpose eq14 eq17)
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq36 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq39 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ (X2 ◇ (v X0))) := by first | exact superpose eq17 eq14 | exact mod_symm (superpose eq17 eq14) | exact superpose eq14 eq17 | exact mod_symm (superpose eq14 eq17)
  have eq40 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X0) ◇ (X3 ◇ X1)) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq46 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = ((e (X0 ◇ X1)) ◇ (e X2)) := by first | exact superpose eq29 eq16 | exact mod_symm (superpose eq29 eq16) | exact superpose eq16 eq29 | exact mod_symm (superpose eq16 eq29)
  have eq47 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq29 eq19 | exact mod_symm (superpose eq29 eq19) | exact superpose eq19 eq29 | exact mod_symm (superpose eq19 eq29)
  have eq49 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq19 eq47 | exact mod_symm (superpose eq19 eq47) | exact superpose eq47 eq19 | exact mod_symm (superpose eq47 eq19)
  have eq50 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = (e ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq16 eq46 | exact mod_symm (superpose eq16 eq46) | exact superpose eq46 eq16 | exact mod_symm (superpose eq46 eq16)
  have eq57 (X0 X1 : G) : (e (X0 ◇ X1)) = (v ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by first | exact superpose eq14 eq21 | exact mod_symm (superpose eq14 eq21) | exact superpose eq21 eq14 | exact mod_symm (superpose eq21 eq14)
  have eq58 (X0 X1 : G) : (v (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq21 eq17 | exact mod_symm (superpose eq21 eq17) | exact superpose eq17 eq21 | exact mod_symm (superpose eq17 eq21)
  have eq59 (X0 X1 : G) : (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq21 eq17 | exact mod_symm (superpose eq21 eq17) | exact superpose eq17 eq21 | exact mod_symm (superpose eq17 eq21)
  have eq60 (X0 X1 : G) : (e (X0 ◇ X1)) = (v ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by first | exact superpose eq41 eq57 | exact mod_symm (superpose eq41 eq57) | exact superpose eq57 eq41 | exact mod_symm (superpose eq57 eq41)
  have eq64 (X0 X1 : G) : (e (X0 ◇ X1)) = (v (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) := by first | exact superpose eq41 eq60 | exact mod_symm (superpose eq41 eq60) | exact superpose eq60 eq41 | exact mod_symm (superpose eq60 eq41)
  have eq82 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq30 eq19 | exact mod_symm (superpose eq30 eq19) | exact superpose eq19 eq30 | exact mod_symm (superpose eq19 eq30)
  have eq84 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq19 eq82 | exact mod_symm (superpose eq19 eq82) | exact superpose eq82 eq19 | exact mod_symm (superpose eq82 eq19)
  have eq93 (X0 X1 : G) : (w (e X0) X1) = (e (v (((e (X0 ◇ X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq16 eq22 | exact mod_symm (superpose eq16 eq22) | exact superpose eq22 eq16 | exact mod_symm (superpose eq22 eq16)
  have eq99 (X0 X1 X2 : G) : (w X1 (X2 ◇ X0)) = (e (v (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2)))) := by first | exact superpose eq14 eq22 | exact mod_symm (superpose eq14 eq22) | exact superpose eq22 eq14 | exact mod_symm (superpose eq22 eq14)
  have eq612 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ (e X1))))) = (e (v (X2 ◇ (e (X0 ◇ X1))))) := by first | exact superpose eq29 eq49 | exact mod_symm (superpose eq29 eq49) | exact superpose eq49 eq29 | exact mod_symm (superpose eq49 eq29)
  have eq613 (X0 X1 X2 : G) : (e (v (X2 ◇ (e (X0 ◇ X1))))) = (e (v (X2 ◇ ((e X0) ◇ X1)))) := by first | exact superpose eq30 eq49 | exact mod_symm (superpose eq30 eq49) | exact superpose eq49 eq30 | exact mod_symm (superpose eq49 eq30)
  have eq619 (X0 X1 : G) : (w X0 (e X1)) = (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq49 eq22 | exact mod_symm (superpose eq49 eq22) | exact superpose eq22 eq49 | exact mod_symm (superpose eq22 eq49)
  have eq626 (X0 X1 X2 : G) : (e (X2 ◇ (v (X0 ◇ (e X1))))) = (e (X2 ◇ (e (v (X0 ◇ X1))))) := by first | exact superpose eq49 eq29 | exact mod_symm (superpose eq49 eq29) | exact superpose eq29 eq49 | exact mod_symm (superpose eq29 eq49)
  have eq629 (X0 X1 X2 : G) : (e (X2 ◇ (v (X0 ◇ (e X1))))) = (e (X2 ◇ (v (X0 ◇ X1)))) := by first | exact superpose eq29 eq626 | exact mod_symm (superpose eq29 eq626) | exact superpose eq626 eq29 | exact mod_symm (superpose eq626 eq29)
  have eq638 (X0 X1 X2 : G) : (e (v (X2 ◇ ((e X0) ◇ X1)))) = (e (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq49 eq613 | exact mod_symm (superpose eq49 eq613) | exact superpose eq613 eq49 | exact mod_symm (superpose eq613 eq49)
  have eq639 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ (e X1))))) = (e (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq49 eq612 | exact mod_symm (superpose eq49 eq612) | exact superpose eq612 eq49 | exact mod_symm (superpose eq612 eq49)
  have eq752 (X0 X1 X2 : G) : (e (v ((X0 ◇ (e X1)) ◇ X2))) = (e (v ((e (X0 ◇ X1)) ◇ X2))) := by first | exact superpose eq29 eq84 | exact mod_symm (superpose eq29 eq84) | exact superpose eq84 eq29 | exact mod_symm (superpose eq84 eq29)
  have eq753 (X0 X1 X2 : G) : (e (v ((e (X0 ◇ X1)) ◇ X2))) = (e (v (((e X0) ◇ X1) ◇ X2))) := by first | exact superpose eq30 eq84 | exact mod_symm (superpose eq30 eq84) | exact superpose eq84 eq30 | exact mod_symm (superpose eq84 eq30)
  have eq794 (X0 X1 X2 : G) : (e (v (((e X0) ◇ X1) ◇ X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq84 eq753 | exact mod_symm (superpose eq84 eq753) | exact superpose eq753 eq84 | exact mod_symm (superpose eq753 eq84)
  have eq795 (X0 X1 X2 : G) : (e (v ((X0 ◇ (e X1)) ◇ X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq84 eq752 | exact mod_symm (superpose eq84 eq752) | exact superpose eq752 eq84 | exact mod_symm (superpose eq752 eq84)
  have eq804 (X0 X1 X2 : G) : ((v X1) ◇ (v (X2 ◇ X0))) = ((v X2) ◇ (v (X0 ◇ X1))) := by first | exact superpose eq17 eq34 | exact mod_symm (superpose eq17 eq34) | exact superpose eq34 eq17 | exact mod_symm (superpose eq34 eq17)
  have eq805 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (v (X1 ◇ X0))) := by first | exact superpose eq20 eq34 | exact mod_symm (superpose eq20 eq34) | exact superpose eq34 eq20 | exact mod_symm (superpose eq34 eq20)
  have eq806 (X0 X1 X2 X3 : G) : (((v X2) ◇ X0) ◇ (v (X3 ◇ X1))) = ((v X3) ◇ (X0 ◇ (v (X1 ◇ X2)))) := by first | exact superpose eq34 eq34 | exact mod_symm (superpose eq34 eq34) | exact superpose eq34 eq34 | exact mod_symm (superpose eq34 eq34)
  have eq807 (X0 X1 X2 : G) : ((e (v X1)) ◇ (v (X2 ◇ X0))) = ((v X2) ◇ (v (X0 ◇ (e X1)))) := by first | exact superpose eq32 eq34 | exact mod_symm (superpose eq32 eq34) | exact superpose eq34 eq32 | exact mod_symm (superpose eq34 eq32)
  have eq809 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = ((v X3) ◇ (X0 ◇ (X1 ◇ (v X2)))) := by first | exact superpose eq14 eq34 | exact mod_symm (superpose eq14 eq34) | exact superpose eq34 eq14 | exact mod_symm (superpose eq34 eq14)
  have eq836 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e X1)))) = ((e (v X1)) ◇ (v (X2 ◇ X0))) := by first | exact superpose eq17 eq807 | exact mod_symm (superpose eq17 eq807) | exact superpose eq807 eq17 | exact mod_symm (superpose eq807 eq17)
  have eq837 (X0 X1 X2 X3 : G) : (((v X2) ◇ X0) ◇ (v (X3 ◇ X1))) = (X0 ◇ (v ((X1 ◇ X2) ◇ X3))) := by first | exact superpose eq39 eq806 | exact mod_symm (superpose eq39 eq806) | exact superpose eq806 eq39 | exact mod_symm (superpose eq806 eq39)
  have eq838 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (((v X0) ◇ (v (X0 ◇ X0))) ◇ (v (X1 ◇ X0))) := by first | exact superpose eq34 eq805 | exact mod_symm (superpose eq34 eq805) | exact superpose eq805 eq34 | exact mod_symm (superpose eq805 eq34)
  have eq839 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ X1))) = ((v X1) ◇ (v (X2 ◇ X0))) := by first | exact superpose eq17 eq804 | exact mod_symm (superpose eq17 eq804) | exact superpose eq804 eq17 | exact mod_symm (superpose eq804 eq17)
  have eq852 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e X1)))) = (v ((e X1) ◇ (X2 ◇ X0))) := by first | exact superpose eq31 eq836 | exact mod_symm (superpose eq31 eq836) | exact superpose eq836 eq31 | exact mod_symm (superpose eq836 eq31)
  have eq853 (X0 X1 : G) : ((v X1) ◇ (e X0)) = ((v (X0 ◇ X0)) ◇ (v ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq837 eq838 | exact mod_symm (superpose eq837 eq838) | exact superpose eq838 eq837 | exact mod_symm (superpose eq838 eq837)
  have eq854 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ X1))) = (v (X1 ◇ (X2 ◇ X0))) := by first | exact superpose eq17 eq839 | exact mod_symm (superpose eq17 eq839) | exact superpose eq839 eq17 | exact mod_symm (superpose eq839 eq17)
  have eq865 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq17 eq853 | exact mod_symm (superpose eq17 eq853) | exact superpose eq853 eq17 | exact mod_symm (superpose eq853 eq17)
  have eq873 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := by first | exact superpose eq41 eq865 | exact mod_symm (superpose eq41 eq865) | exact superpose eq865 eq41 | exact mod_symm (superpose eq865 eq41)
  have eq879 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := by first | exact superpose eq854 eq873 | exact mod_symm (superpose eq854 eq873) | exact superpose eq873 eq854 | exact mod_symm (superpose eq873 eq854)
  have eq885 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by first | exact superpose eq41 eq879 | exact mod_symm (superpose eq41 eq879) | exact superpose eq879 eq41 | exact mod_symm (superpose eq879 eq41)
  have eq1062 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (v (X1 ◇ X2)))) = ((v X2) ◇ ((X0 ◇ (v X1)) ◇ X3)) := by first | exact superpose eq39 eq14 | exact mod_symm (superpose eq39 eq14) | exact superpose eq14 eq39 | exact mod_symm (superpose eq14 eq39)
  have eq1166 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X4 ◇ X2))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq1186 (X0 X1 X2 : G) : ((v X0) ◇ ((((v X0) ◇ ((v X0) ◇ (v X0))) ◇ X1) ◇ X2)) = (X2 ◇ (X1 ◇ (e X0))) := by first | exact superpose eq20 eq35 | exact mod_symm (superpose eq20 eq35) | exact superpose eq35 eq20 | exact mod_symm (superpose eq35 eq20)
  have eq1187 (X0 X1 X2 X3 X4 : G) : ((v X1) ◇ ((((v X2) ◇ X0) ◇ X3) ◇ X4)) = (X4 ◇ (X3 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq34 eq35 | exact mod_symm (superpose eq34 eq35) | exact superpose eq35 eq34 | exact mod_symm (superpose eq35 eq34)
  have eq1188 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X0 ◇ (v (X1 ◇ X2))))) = ((v X2) ◇ (((X0 ◇ (v X1)) ◇ X3) ◇ X4)) := by first | exact superpose eq39 eq35 | exact mod_symm (superpose eq39 eq35) | exact superpose eq35 eq39 | exact mod_symm (superpose eq35 eq39)
  have eq1229 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X1) ◇ X0) ◇ (v (X4 ◇ X2))) = ((v X4) ◇ (X0 ◇ (X1 ◇ ((v X2) ◇ X3)))) := by first | exact superpose eq35 eq34 | exact mod_symm (superpose eq35 eq34) | exact superpose eq34 eq35 | exact mod_symm (superpose eq34 eq35)
  have eq1231 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by first | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14) | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35)
  have eq1249 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ (e X3))))) := by first | exact superpose eq35 eq84 | exact mod_symm (superpose eq35 eq84) | exact superpose eq84 eq35 | exact mod_symm (superpose eq84 eq35)
  have eq1252 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = (X0 ◇ ((X1 ◇ (v X2)) ◇ (v X3))) := by first | exact superpose eq35 eq34 | exact mod_symm (superpose eq35 eq34) | exact superpose eq34 eq35 | exact mod_symm (superpose eq34 eq35)
  have eq1259 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by first | exact superpose eq639 eq1249 | exact mod_symm (superpose eq639 eq1249) | exact superpose eq1249 eq639 | exact mod_symm (superpose eq1249 eq639)
  have eq1294 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = (X2 ◇ (X1 ◇ (((v X0) ◇ (v X0)) ◇ (v (X0 ◇ X0))))) := by first | exact superpose eq1187 eq1186 | exact mod_symm (superpose eq1187 eq1186) | exact superpose eq1186 eq1187 | exact mod_symm (superpose eq1186 eq1187)
  have eq1301 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ ((X1 ◇ (X4 ◇ X2)) ◇ X3)) := by first | exact superpose eq1231 eq1166 | exact mod_symm (superpose eq1231 eq1166) | exact superpose eq1166 eq1231 | exact mod_symm (superpose eq1166 eq1231)
  have eq1350 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = (X2 ◇ ((X1 ◇ (v X0)) ◇ (v ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq1252 eq1294 | exact mod_symm (superpose eq1252 eq1294) | exact superpose eq1294 eq1252 | exact mod_symm (superpose eq1294 eq1252)
  have eq1393 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0))) := by first | exact superpose eq1252 eq1350 | exact mod_symm (superpose eq1252 eq1350) | exact superpose eq1350 eq1252 | exact mod_symm (superpose eq1350 eq1252)
  have eq1951 (X0 X1 X2 X3 X4 : G) : (((v X2) ◇ X0) ◇ ((X4 ◇ (v X1)) ◇ X3)) = (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq34 eq36 | exact mod_symm (superpose eq34 eq36) | exact superpose eq36 eq34 | exact mod_symm (superpose eq36 eq34)
  have eq2070 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ ((X1 ◇ X2) ◇ X0)))) = (e (v (X0 ◇ (X1 ◇ (X2 ◇ (e X3)))))) := by first | exact superpose eq36 eq84 | exact mod_symm (superpose eq36 eq84) | exact superpose eq84 eq36 | exact mod_symm (superpose eq84 eq36)
  have eq2152 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = ((v X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ (v X1)))) := by first | exact superpose eq1231 eq1951 | exact mod_symm (superpose eq1231 eq1951) | exact superpose eq1951 eq1231 | exact mod_symm (superpose eq1951 eq1231)
  have eq2212 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = (((X0 ◇ X3) ◇ X4) ◇ (v (X2 ◇ X1))) := by first | exact superpose eq809 eq2152 | exact mod_symm (superpose eq809 eq2152) | exact superpose eq2152 eq809 | exact mod_symm (superpose eq2152 eq809)
  have eq2607 (X0 X1 X2 X3 X4 : G) : (v (X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = (v ((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X3))) := by first | exact superpose eq35 eq854 | exact mod_symm (superpose eq35 eq854) | exact superpose eq854 eq35 | exact mod_symm (superpose eq854 eq35)
  have eq2625 (X0 X1 X2 X3 : G) : (v (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (v (X0 ◇ (X2 ◇ (X3 ◇ X1)))) := by first | exact superpose eq35 eq854 | exact mod_symm (superpose eq35 eq854) | exact superpose eq854 eq35 | exact mod_symm (superpose eq854 eq35)
  have eq2637 (X0 X1 X2 X3 X4 : G) : (v (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (v (X2 ◇ (((X3 ◇ X1) ◇ X0) ◇ X4))) := by first | exact superpose eq35 eq854 | exact mod_symm (superpose eq35 eq854) | exact superpose eq854 eq35 | exact mod_symm (superpose eq854 eq35)
  have eq2651 (X0 X1 X2 X3 : G) : (v (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (v (X2 ◇ ((X0 ◇ X1) ◇ X3))) := by first | exact superpose eq35 eq854 | exact mod_symm (superpose eq35 eq854) | exact superpose eq854 eq35 | exact mod_symm (superpose eq854 eq35)
  have eq2675 (X0 X1 X2 X3 : G) : (v ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = ((v (X0 ◇ (X1 ◇ X2))) ◇ (v X3)) := by first | exact superpose eq854 eq17 | exact mod_symm (superpose eq854 eq17) | exact superpose eq17 eq854 | exact mod_symm (superpose eq17 eq854)
  have eq2685 (X0 X1 X2 X3 X4 : G) : ((v (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (v X4))) = (X3 ◇ (v (X4 ◇ (X2 ◇ (X0 ◇ X1))))) := by first | exact superpose eq854 eq39 | exact mod_symm (superpose eq854 eq39) | exact superpose eq39 eq854 | exact mod_symm (superpose eq39 eq854)
  have eq2686 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (v (X4 ◇ (X2 ◇ (X0 ◇ X1))))) = (X3 ◇ (v (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by first | exact superpose eq39 eq2685 | exact mod_symm (superpose eq39 eq2685) | exact superpose eq2685 eq39 | exact mod_symm (superpose eq2685 eq39)
  have eq2696 (X0 X1 X2 X3 : G) : (v ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (v ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by first | exact superpose eq17 eq2675 | exact mod_symm (superpose eq17 eq2675) | exact superpose eq2675 eq17 | exact mod_symm (superpose eq2675 eq17)
  have eq2725 (X0 X1 X2 X3 X4 : G) : (v (X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = (v (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X4))) := by first | exact superpose eq1231 eq2607 | exact mod_symm (superpose eq1231 eq2607) | exact superpose eq2607 eq1231 | exact mod_symm (superpose eq2607 eq1231)
  have eq2932 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X3 ◇ X1) ◇ (((X0 ◇ X2) ◇ X4) ◇ X5)) := by first | exact superpose eq40 eq35 | exact mod_symm (superpose eq40 eq35) | exact superpose eq35 eq40 | exact mod_symm (superpose eq35 eq40)
  have eq2947 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X3 ◇ ((X1 ◇ X5) ◇ ((X0 ◇ X2) ◇ X4))) := by first | exact superpose eq1231 eq2932 | exact mod_symm (superpose eq1231 eq2932) | exact superpose eq2932 eq1231 | exact mod_symm (superpose eq2932 eq1231)
  have eq3089 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X3 ◇ (X1 ◇ ((X5 ◇ X4) ◇ (X0 ◇ X2)))) := by first | exact superpose eq1231 eq2947 | exact mod_symm (superpose eq1231 eq2947) | exact superpose eq2947 eq1231 | exact mod_symm (superpose eq2947 eq1231)
  have eq3172 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X3 ◇ (X1 ◇ (X5 ◇ ((X4 ◇ X2) ◇ X0)))) := by first | exact superpose eq1231 eq3089 | exact mod_symm (superpose eq1231 eq3089) | exact superpose eq3089 eq1231 | exact mod_symm (superpose eq3089 eq1231)
  have eq3615 (X0 X1 X2 X3 : G) : (e (v (((X0 ◇ (e X1)) ◇ X2) ◇ X3))) = (e (v ((e ((X0 ◇ X1) ◇ X2)) ◇ X3))) := by first | exact superpose eq50 eq84 | exact mod_symm (superpose eq50 eq84) | exact superpose eq84 eq50 | exact mod_symm (superpose eq84 eq50)
  have eq3616 (X0 X1 X2 X3 : G) : (e (v (((X0 ◇ (e X1)) ◇ X2) ◇ X3))) = (e (v (((X0 ◇ X1) ◇ X2) ◇ X3))) := by first | exact superpose eq84 eq3615 | exact mod_symm (superpose eq84 eq3615) | exact superpose eq3615 eq84 | exact mod_symm (superpose eq3615 eq84)
  have eq3770 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = ((v X0) ◇ (X1 ◇ (X2 ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))))) := by first | exact superpose eq20 eq41 | exact mod_symm (superpose eq20 eq41) | exact superpose eq41 eq20 | exact mod_symm (superpose eq41 eq20)
  have eq3970 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = (((((v X0) ◇ (v X0)) ◇ X2) ◇ X1) ◇ (v (X0 ◇ X0))) := by first | exact superpose eq1229 eq3770 | exact mod_symm (superpose eq1229 eq3770) | exact superpose eq3770 eq1229 | exact mod_symm (superpose eq3770 eq1229)
  have eq4099 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (((v X0) ◇ (v X0)) ◇ (v (X0 ◇ X0))))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq2212 eq3970 | exact mod_symm (superpose eq2212 eq3970) | exact superpose eq3970 eq2212 | exact mod_symm (superpose eq3970 eq2212)
  have eq4169 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (v X0)) ◇ (v ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1252 eq4099 | exact mod_symm (superpose eq1252 eq4099) | exact superpose eq4099 eq1252 | exact mod_symm (superpose eq4099 eq1252)
  have eq4213 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1252 eq4169 | exact mod_symm (superpose eq1252 eq4169) | exact superpose eq4169 eq1252 | exact mod_symm (superpose eq4169 eq1252)
  have eq4244 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1393 eq4213 | exact mod_symm (superpose eq1393 eq4213) | exact superpose eq4213 eq1393 | exact mod_symm (superpose eq4213 eq1393)
  have eq4506 (X0 X1 X2 : G) : ((v X1) ◇ ((v X0) ◇ (e X2))) = ((v (X0 ◇ X1)) ◇ (e X2)) := by first | exact superpose eq17 eq4244 | exact mod_symm (superpose eq17 eq4244) | exact superpose eq4244 eq17 | exact mod_symm (superpose eq4244 eq17)
  have eq4525 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (X0 ◇ (e X1))) ◇ (e X1)))) := by first | exact superpose eq4244 eq22 | exact mod_symm (superpose eq4244 eq22) | exact superpose eq22 eq4244 | exact mod_symm (superpose eq22 eq4244)
  have eq4532 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ (e X2))))) = (e (v ((X1 ◇ X0) ◇ X2))) := by first | exact superpose eq4244 eq49 | exact mod_symm (superpose eq4244 eq49) | exact superpose eq49 eq4244 | exact mod_symm (superpose eq49 eq4244)
  have eq4565 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ X2)))) = (e (v ((X1 ◇ X0) ◇ X2))) := by first | exact superpose eq639 eq4532 | exact mod_symm (superpose eq639 eq4532) | exact superpose eq4532 eq639 | exact mod_symm (superpose eq4532 eq639)
  have eq4570 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (X0 ◇ (e X1))) ◇ X1))) := by first | exact superpose eq49 eq4525 | exact mod_symm (superpose eq49 eq4525) | exact superpose eq4525 eq49 | exact mod_symm (superpose eq4525 eq49)
  have eq4577 (X0 X1 X2 : G) : ((v (X0 ◇ X1)) ◇ (e X2)) = ((e X2) ◇ (v (X1 ◇ X0))) := by first | exact superpose eq34 eq4506 | exact mod_symm (superpose eq34 eq4506) | exact superpose eq4506 eq34 | exact mod_symm (superpose eq4506 eq34)
  have eq4608 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (e X1)) ◇ (X0 ◇ X1)))) := by first | exact superpose eq4565 eq4570 | exact mod_symm (superpose eq4565 eq4570) | exact superpose eq4570 eq4565 | exact mod_symm (superpose eq4570 eq4565)
  have eq4636 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by first | exact superpose eq795 eq4608 | exact mod_symm (superpose eq795 eq4608) | exact superpose eq4608 eq795 | exact mod_symm (superpose eq4608 eq795)
  have eq4658 (X0 X1 : G) : (w X0 (e X1)) = (e (v (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by first | exact superpose eq4565 eq4636 | exact mod_symm (superpose eq4565 eq4636) | exact superpose eq4636 eq4565 | exact mod_symm (superpose eq4636 eq4565)
  have eq4753 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((e (X0 ◇ (e X0))) ◇ X1) ◇ X1))) := by first | exact superpose eq30 eq93 | exact mod_symm (superpose eq30 eq93) | exact superpose eq93 eq30 | exact mod_symm (superpose eq93 eq30)
  have eq4755 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e ((X0 ◇ X0) ◇ X1)) ◇ (e X1)))) := by first | exact superpose eq16 eq93 | exact mod_symm (superpose eq16 eq93) | exact superpose eq93 eq16 | exact mod_symm (superpose eq93 eq16)
  have eq4780 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (((e (X0 ◇ X0)) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq93 eq49 | exact mod_symm (superpose eq93 eq49) | exact superpose eq49 eq93 | exact mod_symm (superpose eq49 eq93)
  have eq4802 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq794 eq4780 | exact mod_symm (superpose eq794 eq4780) | exact superpose eq4780 eq794 | exact mod_symm (superpose eq4780 eq794)
  have eq4826 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e ((X0 ◇ X0) ◇ X1)) ◇ X1))) := by first | exact superpose eq49 eq4755 | exact mod_symm (superpose eq49 eq4755) | exact superpose eq4755 eq49 | exact mod_symm (superpose eq4755 eq49)
  have eq4828 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((X0 ◇ (e X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq794 eq4753 | exact mod_symm (superpose eq794 eq4753) | exact superpose eq4753 eq794 | exact mod_symm (superpose eq4753 eq794)
  have eq4850 (X0 X1 : G) : (w X0 (e X1)) = (w (e X0) (e X1)) := by first | exact superpose eq619 eq4802 | exact mod_symm (superpose eq619 eq4802) | exact superpose eq4802 eq619 | exact mod_symm (superpose eq4802 eq619)
  have eq4874 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq84 eq4826 | exact mod_symm (superpose eq84 eq4826) | exact superpose eq4826 eq84 | exact mod_symm (superpose eq4826 eq84)
  have eq4876 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e (e X0)) X1) := by first | exact superpose eq3616 eq4828 | exact mod_symm (superpose eq3616 eq4828) | exact superpose eq4828 eq3616 | exact mod_symm (superpose eq4828 eq3616)
  have eq4917 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w X0 (e X1)) := by first | exact superpose eq4850 eq4874 | exact mod_symm (superpose eq4850 eq4874) | exact superpose eq4874 eq4850 | exact mod_symm (superpose eq4874 eq4850)
  have eq4918 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e X0) X1) := by first | exact superpose eq18 eq4876 | exact mod_symm (superpose eq18 eq4876) | exact superpose eq4876 eq18 | exact mod_symm (superpose eq4876 eq18)
  have eq4944 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq22 eq4917 | exact mod_symm (superpose eq22 eq4917) | exact superpose eq4917 eq22 | exact mod_symm (superpose eq4917 eq22)
  have eq4945 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq22 eq4918 | exact mod_symm (superpose eq22 eq4918) | exact superpose eq4918 eq22 | exact mod_symm (superpose eq4918 eq22)
  have eq5461 (X0 X1 X2 : G) : ((v (X2 ◇ X1)) ◇ (e X0)) = (v (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)))) := by first | exact superpose eq40 eq58 | exact mod_symm (superpose eq40 eq58) | exact superpose eq58 eq40 | exact mod_symm (superpose eq58 eq40)
  have eq5466 (X0 X1 : G) : ((v X0) ◇ (e X1)) = (v (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) := by first | exact superpose eq58 eq854 | exact mod_symm (superpose eq58 eq854) | exact superpose eq854 eq58 | exact mod_symm (superpose eq854 eq58)
  have eq5475 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) = ((v X2) ◇ ((v X0) ◇ (e X1))) := by first | exact superpose eq58 eq17 | exact mod_symm (superpose eq58 eq17) | exact superpose eq17 eq58 | exact mod_symm (superpose eq17 eq58)
  have eq5495 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) = ((e X1) ◇ (v (X2 ◇ X0))) := by first | exact superpose eq34 eq5475 | exact mod_symm (superpose eq34 eq5475) | exact superpose eq5475 eq34 | exact mod_symm (superpose eq5475 eq34)
  have eq5503 (X0 X1 : G) : ((v X0) ◇ (e X1)) = (v (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq1301 eq5466 | exact mod_symm (superpose eq1301 eq5466) | exact superpose eq5466 eq1301 | exact mod_symm (superpose eq5466 eq1301)
  have eq5819 (X0 X1 X2 X3 : G) : (v (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3)))))) = ((e X3) ◇ (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq35 eq59 | exact mod_symm (superpose eq35 eq59) | exact superpose eq59 eq35 | exact mod_symm (superpose eq59 eq35)
  have eq5834 (X0 X1 : G) : (e (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) = (e ((e X0) ◇ (v (e X1)))) := by first | exact superpose eq59 eq49 | exact mod_symm (superpose eq59 eq49) | exact superpose eq49 eq59 | exact mod_symm (superpose eq49 eq59)
  have eq5863 (X0 X1 : G) : (e (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) = (e (X0 ◇ (v (e X1)))) := by first | exact superpose eq30 eq5834 | exact mod_symm (superpose eq30 eq5834) | exact superpose eq5834 eq30 | exact mod_symm (superpose eq5834 eq30)
  have eq5872 (X0 X1 X2 X3 : G) : ((e X3) ◇ (v (X2 ◇ (X0 ◇ X1)))) = ((e X3) ◇ (v (X0 ◇ (X1 ◇ X2)))) := by first | exact superpose eq5495 eq5819 | exact mod_symm (superpose eq5495 eq5819) | exact superpose eq5819 eq5495 | exact mod_symm (superpose eq5819 eq5495)
  have eq5919 (X0 X1 : G) : (e (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) = (e (X0 ◇ (e (v X1)))) := by first | exact superpose eq19 eq5863 | exact mod_symm (superpose eq19 eq5863) | exact superpose eq5863 eq19 | exact mod_symm (superpose eq5863 eq19)
  have eq5966 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) := by first | exact superpose eq29 eq5919 | exact mod_symm (superpose eq29 eq5919) | exact superpose eq5919 eq29 | exact mod_symm (superpose eq5919 eq29)
  have eq6005 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))) := by first | exact superpose eq4565 eq5966 | exact mod_symm (superpose eq4565 eq5966) | exact superpose eq5966 eq4565 | exact mod_symm (superpose eq5966 eq4565)
  have eq6033 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) := by first | exact superpose eq4565 eq6005 | exact mod_symm (superpose eq4565 eq6005) | exact superpose eq6005 eq4565 | exact mod_symm (superpose eq6005 eq4565)
  have eq6055 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := by first | exact superpose eq4565 eq6033 | exact mod_symm (superpose eq4565 eq6033) | exact superpose eq6033 eq4565 | exact mod_symm (superpose eq6033 eq4565)
  have eq6072 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e ((v X1) ◇ (e X0))) := by first | exact superpose eq5503 eq6055 | exact mod_symm (superpose eq5503 eq6055) | exact superpose eq6055 eq5503 | exact mod_symm (superpose eq6055 eq5503)
  have eq6088 (X0 X1 : G) : (e ((v X1) ◇ X0)) = (e (X0 ◇ (v X1))) := by first | exact superpose eq29 eq6072 | exact mod_symm (superpose eq29 eq6072) | exact superpose eq6072 eq29 | exact mod_symm (superpose eq6072 eq29)
  have eq6440 (X0 X1 : G) : (e ((e X0) ◇ X1)) = (e (X1 ◇ (e X0))) := by first | exact superpose eq21 eq6088 | exact mod_symm (superpose eq21 eq6088) | exact superpose eq6088 eq21 | exact mod_symm (superpose eq6088 eq21)
  have eq6540 (X0 X1 : G) : (e ((e X0) ◇ X1)) = (e (X1 ◇ X0)) := by first | exact superpose eq29 eq6440 | exact mod_symm (superpose eq29 eq6440) | exact superpose eq6440 eq29 | exact mod_symm (superpose eq6440 eq29)
  have eq6915 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((e ((e X0) ◇ X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq6540 eq93 | exact mod_symm (superpose eq6540 eq93) | exact superpose eq93 eq6540 | exact mod_symm (superpose eq93 eq6540)
  have eq6932 (X0 X1 X2 : G) : (e (v (X2 ◇ (e (X0 ◇ X1))))) = (e (v (X2 ◇ ((e X1) ◇ X0)))) := by first | exact superpose eq6540 eq49 | exact mod_symm (superpose eq6540 eq49) | exact superpose eq49 eq6540 | exact mod_symm (superpose eq49 eq6540)
  have eq6945 (X0 X1 X2 : G) : (e (v (X2 ◇ (e (X0 ◇ X1))))) = (e (v (X2 ◇ (X1 ◇ X0)))) := by first | exact superpose eq638 eq6932 | exact mod_symm (superpose eq638 eq6932) | exact superpose eq6932 eq638 | exact mod_symm (superpose eq6932 eq638)
  have eq6960 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v ((((e X0) ◇ X0) ◇ X1) ◇ X1))) := by first | exact superpose eq794 eq6915 | exact mod_symm (superpose eq794 eq6915) | exact superpose eq6915 eq794 | exact mod_symm (superpose eq6915 eq794)
  have eq7001 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ X1)))) = (e (v (X2 ◇ (X1 ◇ X0)))) := by first | exact superpose eq49 eq6945 | exact mod_symm (superpose eq49 eq6945) | exact superpose eq6945 eq49 | exact mod_symm (superpose eq6945 eq49)
  have eq7011 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (X1 ◇ (((e X0) ◇ X0) ◇ X1)))) := by first | exact superpose eq4565 eq6960 | exact mod_symm (superpose eq4565 eq6960) | exact superpose eq6960 eq4565 | exact mod_symm (superpose eq6960 eq4565)
  have eq7043 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (X1 ◇ (X0 ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq1259 eq7011 | exact mod_symm (superpose eq1259 eq7011) | exact superpose eq7011 eq1259 | exact mod_symm (superpose eq7011 eq1259)
  have eq7061 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := by first | exact superpose eq2070 eq7043 | exact mod_symm (superpose eq2070 eq7043) | exact superpose eq7043 eq2070 | exact mod_symm (superpose eq7043 eq2070)
  have eq7064 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq7001 eq7061 | exact mod_symm (superpose eq7001 eq7061) | exact superpose eq7061 eq7001 | exact mod_symm (superpose eq7061 eq7001)
  have eq7065 (X0 X1 : G) : (w (e X0) X1) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq4945 eq7064 | exact mod_symm (superpose eq4945 eq7064) | exact superpose eq7064 eq4945 | exact mod_symm (superpose eq7064 eq4945)
  have eq7066 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq4945 eq7065 | exact mod_symm (superpose eq4945 eq7065) | exact superpose eq7065 eq4945 | exact mod_symm (superpose eq7065 eq4945)
  have eq8925 (X0 X1 : G) : (w X1 (e X0)) = (e (v (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (((X1 ◇ X1) ◇ (e X0)) ◇ (v X0))))) := by first | exact superpose eq20 eq99 | exact mod_symm (superpose eq20 eq99) | exact superpose eq99 eq20 | exact mod_symm (superpose eq99 eq20)
  have eq9037 (X0 X1 : G) : (w X1 (e X0)) = (e (v (((v X0) ◇ (v X0)) ◇ ((v X0) ◇ (((X1 ◇ X1) ◇ (e X0)) ◇ (v X0)))))) := by first | exact superpose eq4565 eq8925 | exact mod_symm (superpose eq4565 eq8925) | exact superpose eq8925 eq4565 | exact mod_symm (superpose eq8925 eq4565)
  have eq9116 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (((X1 ◇ X1) ◇ (e X0)) ◇ (v X0))))))) := by first | exact superpose eq4565 eq9037 | exact mod_symm (superpose eq4565 eq9037) | exact superpose eq9037 eq4565 | exact mod_symm (superpose eq9037 eq4565)
  have eq9181 (X0 X1 : G) : (w X1 (e X0)) = (e ((v ((X1 ◇ X1) ◇ (e X0))) ◇ (e (v X0)))) := by first | exact superpose eq885 eq9116 | exact mod_symm (superpose eq885 eq9116) | exact superpose eq9116 eq885 | exact mod_symm (superpose eq9116 eq885)
  have eq9230 (X0 X1 : G) : (w X1 (e X0)) = (e ((v ((X1 ◇ X1) ◇ (e X0))) ◇ (v X0))) := by first | exact superpose eq29 eq9181 | exact mod_symm (superpose eq29 eq9181) | exact superpose eq9181 eq29 | exact mod_symm (superpose eq9181 eq29)
  have eq9266 (X0 X1 : G) : (w X1 (e X0)) = (e ((v X0) ◇ (v ((X1 ◇ X1) ◇ (e X0))))) := by first | exact superpose eq6088 eq9230 | exact mod_symm (superpose eq6088 eq9230) | exact superpose eq9230 eq6088 | exact mod_symm (superpose eq9230 eq6088)
  have eq9292 (X0 X1 : G) : (w X1 (e X0)) = (e ((v X0) ◇ (v ((X1 ◇ X1) ◇ X0)))) := by first | exact superpose eq629 eq9266 | exact mod_symm (superpose eq629 eq9266) | exact superpose eq9266 eq629 | exact mod_symm (superpose eq9266 eq629)
  have eq9311 (X0 X1 : G) : (w X1 (e X0)) = (e (v (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by first | exact superpose eq17 eq9292 | exact mod_symm (superpose eq17 eq9292) | exact superpose eq9292 eq17 | exact mod_symm (superpose eq9292 eq17)
  have eq9323 (X0 X1 : G) : (w X1 (e X0)) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq1259 eq9311 | exact mod_symm (superpose eq1259 eq9311) | exact superpose eq9311 eq1259 | exact mod_symm (superpose eq9311 eq1259)
  have eq9332 (X0 X1 : G) : (w X0 X1) = (w X1 (e X0)) := by first | exact superpose eq7066 eq9323 | exact mod_symm (superpose eq7066 eq9323) | exact superpose eq9323 eq7066 | exact mod_symm (superpose eq9323 eq7066)
  have eq10234 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0)))))))) := by first | exact superpose eq20 eq64 | exact mod_symm (superpose eq20 eq64) | exact superpose eq64 eq20 | exact mod_symm (superpose eq64 eq20)
  have eq10357 (X0 : G) : (e (e X0)) = ((v ((((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0)))) ◇ (v X0))) ◇ (e (v X0))) := by first | exact superpose eq5461 eq10234 | exact mod_symm (superpose eq5461 eq10234) | exact superpose eq10234 eq5461 | exact mod_symm (superpose eq10234 eq5461)
  have eq10423 (X0 : G) : (e (e X0)) = (v (((((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0)))) ◇ (v X0)) ◇ (e X0))) := by first | exact superpose eq32 eq10357 | exact mod_symm (superpose eq32 eq10357) | exact superpose eq10357 eq32 | exact mod_symm (superpose eq10357 eq32)
  have eq10489 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ ((((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0)))) ◇ (e X0)))) := by first | exact superpose eq4244 eq10423 | exact mod_symm (superpose eq4244 eq10423) | exact superpose eq10423 eq4244 | exact mod_symm (superpose eq10423 eq4244)
  have eq10551 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0))))))) := by first | exact superpose eq852 eq10489 | exact mod_symm (superpose eq852 eq10489) | exact superpose eq10489 eq852 | exact mod_symm (superpose eq10489 eq852)
  have eq10609 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((v X0) ◇ ((e X0) ◇ (((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))))))) := by first | exact superpose eq3172 eq10551 | exact mod_symm (superpose eq3172 eq10551) | exact superpose eq10551 eq3172 | exact mod_symm (superpose eq10551 eq3172)
  have eq10659 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((e X0) ◇ ((((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ (v X0))))) := by first | exact superpose eq2625 eq10609 | exact mod_symm (superpose eq2625 eq10609) | exact superpose eq10609 eq2625 | exact mod_symm (superpose eq10609 eq2625)
  have eq10703 (X0 : G) : (e (e X0)) = (v (((((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ (v X0)) ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq33 eq10659 | exact mod_symm (superpose eq33 eq10659) | exact superpose eq10659 eq33 | exact mod_symm (superpose eq10659 eq33)
  have eq10745 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ ((((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq4244 eq10703 | exact mod_symm (superpose eq4244 eq10703) | exact superpose eq10703 eq4244 | exact mod_symm (superpose eq10703 eq4244)
  have eq10784 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (v (X0 ◇ X0)))))) := by first | exact superpose eq1187 eq10745 | exact mod_symm (superpose eq1187 eq10745) | exact superpose eq10745 eq1187 | exact mod_symm (superpose eq10745 eq1187)
  have eq10822 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v (X0 ◇ X0)) ◇ ((v X0) ◇ ((v X0) ◇ (v X0))))))) := by first | exact superpose eq2625 eq10784 | exact mod_symm (superpose eq2625 eq10784) | exact superpose eq10784 eq2625 | exact mod_symm (superpose eq10784 eq2625)
  have eq10857 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ (((((v X0) ◇ (v X0)) ◇ (v (X0 ◇ X0))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq2637 eq10822 | exact mod_symm (superpose eq2637 eq10822) | exact superpose eq10822 eq2637 | exact mod_symm (superpose eq10822 eq2637)
  have eq10889 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (((v X0) ◇ (v X0)) ◇ (v ((X0 ◇ X0) ◇ X0)))))) := by first | exact superpose eq1188 eq10857 | exact mod_symm (superpose eq1188 eq10857) | exact superpose eq10857 eq1188 | exact mod_symm (superpose eq10857 eq1188)
  have eq10916 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ (v X0)) ◇ ((v ((X0 ◇ X0) ◇ X0)) ◇ ((v X0) ◇ ((v X0) ◇ (v X0))))))) := by first | exact superpose eq2625 eq10889 | exact mod_symm (superpose eq2625 eq10889) | exact superpose eq10889 eq2625 | exact mod_symm (superpose eq10889 eq2625)
  have eq10937 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ (((((v X0) ◇ (v X0)) ◇ (v ((X0 ◇ X0) ◇ X0))) ◇ ((v X0) ◇ (v X0))) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq2637 eq10916 | exact mod_symm (superpose eq2637 eq10916) | exact superpose eq10916 eq2637 | exact mod_symm (superpose eq10916 eq2637)
  have eq10955 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ (v X0)) ◇ (((v X0) ◇ (v X0)) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0)))))) := by first | exact superpose eq1188 eq10937 | exact mod_symm (superpose eq1188 eq10937) | exact superpose eq10937 eq1188 | exact mod_symm (superpose eq10937 eq1188)
  have eq10972 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ (((((v X0) ◇ (v X0)) ◇ (v X0)) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq2725 eq10955 | exact mod_symm (superpose eq2725 eq10955) | exact superpose eq10955 eq2725 | exact mod_symm (superpose eq10955 eq2725)
  have eq10989 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ ((((v X0) ◇ (v X0)) ◇ (v X0)) ◇ (v ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))))) := by first | exact superpose eq1062 eq10972 | exact mod_symm (superpose eq1062 eq10972) | exact superpose eq10972 eq1062 | exact mod_symm (superpose eq10972 eq1062)
  have eq11006 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ (((e (X0 ◇ X0)) ◇ ((v X0) ◇ (v X0))) ◇ (v ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))))) := by first | exact superpose eq2651 eq10989 | exact mod_symm (superpose eq2651 eq10989) | exact superpose eq10989 eq2651 | exact mod_symm (superpose eq10989 eq2651)
  have eq11022 (X0 : G) : (e (e X0)) = (v (((e (X0 ◇ X0)) ◇ ((v X0) ◇ (v X0))) ◇ (v (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0)))) := by first | exact superpose eq39 eq11006 | exact mod_symm (superpose eq39 eq11006) | exact superpose eq11006 eq39 | exact mod_symm (superpose eq11006 eq39)
  have eq11035 (X0 : G) : (e (e X0)) = (v (((v X0) ◇ ((v X0) ◇ (e (X0 ◇ X0)))) ◇ (v (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0)))) := by first | exact superpose eq2696 eq11022 | exact mod_symm (superpose eq2696 eq11022) | exact superpose eq11022 eq2696 | exact mod_symm (superpose eq11022 eq2696)
  have eq11047 (X0 : G) : (e (e X0)) = (v (((v X0) ◇ (e (X0 ◇ X0))) ◇ (v ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))))) := by first | exact superpose eq837 eq11035 | exact mod_symm (superpose eq837 eq11035) | exact superpose eq11035 eq837 | exact mod_symm (superpose eq11035 eq837)
  have eq11059 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (v ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) := by first | exact superpose eq837 eq11047 | exact mod_symm (superpose eq837 eq11047) | exact superpose eq11047 eq837 | exact mod_symm (superpose eq11047 eq837)
  have eq11070 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (v (X0 ◇ (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0)))))) := by first | exact superpose eq5872 eq11059 | exact mod_symm (superpose eq5872 eq11059) | exact superpose eq11059 eq5872 | exact mod_symm (superpose eq11059 eq5872)
  have eq11079 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (v (X0 ◇ (X0 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))))))) := by first | exact superpose eq2686 eq11070 | exact mod_symm (superpose eq2686 eq11070) | exact superpose eq11070 eq2686 | exact mod_symm (superpose eq11070 eq2686)
  have eq11087 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ ((v (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (e X0)))) := by first | exact superpose eq885 eq11079 | exact mod_symm (superpose eq885 eq11079) | exact superpose eq11079 eq885 | exact mod_symm (superpose eq11079 eq885)
  have eq11091 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((e (X0 ◇ X0)) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0))))) := by first | exact superpose eq852 eq11087 | exact mod_symm (superpose eq852 eq11087) | exact superpose eq11087 eq852 | exact mod_symm (superpose eq11087 eq852)
  have eq11094 (X0 : G) : (e (e X0)) = (v ((v (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (e (X0 ◇ (X0 ◇ X0))))) := by first | exact superpose eq33 eq11091 | exact mod_symm (superpose eq33 eq11091) | exact superpose eq11091 eq33 | exact mod_symm (superpose eq11091 eq33)
  have eq11097 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ (X0 ◇ X0))) ◇ (v (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := by first | exact superpose eq4577 eq11094 | exact mod_symm (superpose eq4577 eq11094) | exact superpose eq11094 eq4577 | exact mod_symm (superpose eq11094 eq4577)
  have eq11100 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ (X0 ◇ X0))) ◇ (v (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by first | exact superpose eq5872 eq11097 | exact mod_symm (superpose eq5872 eq11097) | exact superpose eq11097 eq5872 | exact mod_symm (superpose eq11097 eq5872)
  have eq11102 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ (X0 ◇ X0))) ◇ (e X0))) := by first | exact superpose eq21 eq11100 | exact mod_symm (superpose eq21 eq11100) | exact superpose eq11100 eq21 | exact mod_symm (superpose eq11100 eq21)
  have eq11104 (X0 : G) : (e (e X0)) = (v (e ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := by first | exact superpose eq16 eq11102 | exact mod_symm (superpose eq16 eq11102) | exact superpose eq11102 eq16 | exact mod_symm (superpose eq11102 eq16)
  have eq11105 (X0 : G) : (e (e X0)) = (e (v ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := by first | exact superpose eq19 eq11104 | exact mod_symm (superpose eq19 eq11104) | exact superpose eq11104 eq19 | exact mod_symm (superpose eq11104 eq19)
  have eq11106 (X0 : G) : (e (e X0)) = (e (v ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by first | exact superpose eq4565 eq11105 | exact mod_symm (superpose eq4565 eq11105) | exact superpose eq11105 eq4565 | exact mod_symm (superpose eq11105 eq4565)
  have eq11107 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by first | exact superpose eq4565 eq11106 | exact mod_symm (superpose eq4565 eq11106) | exact superpose eq11106 eq4565 | exact mod_symm (superpose eq11106 eq4565)
  have eq11108 (X0 : G) : (e (e X0)) = (w X0 (e X0)) := by first | exact superpose eq4658 eq11107 | exact mod_symm (superpose eq4658 eq11107) | exact superpose eq11107 eq4658 | exact mod_symm (superpose eq11107 eq4658)
  have eq11109 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq4944 eq11108 | exact mod_symm (superpose eq4944 eq11108) | exact superpose eq11108 eq4944 | exact mod_symm (superpose eq11108 eq4944)
  have eq11110 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq18 eq11109 | exact mod_symm (superpose eq18 eq11109) | exact superpose eq11109 eq18 | exact mod_symm (superpose eq11109 eq18)
  have eq11130 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq11110 eq23 | exact mod_symm (superpose eq11110 eq23) | exact superpose eq23 eq11110 | exact mod_symm (superpose eq23 eq11110)
  subsumption eq11130 eq9332


/-- Equation 4343 `x ◇ (y ◇ y) = y ◇ (x ◇ x)` is term-definable from equation 4364 over finite magmas, via the term
`x □ y := (((x ◇ x) ◇ y) ◇ y)` with `u a = (a ◇ (a ◇ (a ◇ a)))`
taken at u^[2N+1]. -/
private theorem aux4364_4343 [Magma G] (h : Equation4364 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huh : ∀ a b : G, ((a ◇ b) ◇ ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ b)))) = (a ◇ (a ◇ (a ◇ a))) ◇ (b ◇ (b ◇ (b ◇ b))))
    (huv : ∀ a : G, ((v a) ◇ ((v a) ◇ ((v a) ◇ (v a)))) = e a)
    (hvu : ∀ a : G, v (a ◇ (a ◇ (a ◇ a))) = e a)
    (hw : ∀ a b : G, w a b = (e (v ((((a ◇ a) ◇ b) ◇ b)))))
    (x y : G) :
    (w x (w y y)) =
      (w y (w x x)) := by
  by_contra nh
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have eq16 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq17 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq18 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq19 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq20 (X0 : G) : (e X0) = ((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) := mod_symm (huv ..)
  have eq21 (X0 : G) : (e X0) = (v (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := mod_symm (hvu ..)
  have eq22 (X0 X1 : G) : (w X0 X1) = (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) := mod_symm (hw ..)
  have eq23 : (w x (w y y)) ≠ (w y (w x x)) := mod_symm nh
  have eq27 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq18 eq16 | exact mod_symm (superpose eq18 eq16) | exact superpose eq16 eq18 | exact mod_symm (superpose eq16 eq18)
  have eq28 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq18 eq16 | exact mod_symm (superpose eq18 eq16) | exact superpose eq16 eq18 | exact mod_symm (superpose eq16 eq18)
  have eq29 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq16 eq28 | exact mod_symm (superpose eq16 eq28) | exact superpose eq28 eq16 | exact mod_symm (superpose eq28 eq16)
  have eq30 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq27 | exact mod_symm (superpose eq16 eq27) | exact superpose eq27 eq16 | exact mod_symm (superpose eq27 eq16)
  have eq31 (X0 X1 : G) : (v ((e X0) ◇ X1)) = ((e (v X0)) ◇ (v X1)) := by first | exact superpose eq19 eq17 | exact mod_symm (superpose eq19 eq17) | exact superpose eq17 eq19 | exact mod_symm (superpose eq17 eq19)
  have eq32 (X0 X1 : G) : (v (X1 ◇ (e X0))) = ((v X1) ◇ (e (v X0))) := by first | exact superpose eq19 eq17 | exact mod_symm (superpose eq19 eq17) | exact superpose eq17 eq19 | exact mod_symm (superpose eq17 eq19)
  have eq33 (X0 X1 X2 : G) : ((e X0) ◇ ((e X1) ◇ X2)) = (X2 ◇ (e (X0 ◇ X1))) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq34 (X0 X1 X2 : G) : ((v X0) ◇ ((v X1) ◇ X2)) = (X2 ◇ (v (X0 ◇ X1))) := by first | exact superpose eq17 eq14 | exact mod_symm (superpose eq17 eq14) | exact superpose eq14 eq17 | exact mod_symm (superpose eq14 eq17)
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq36 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq39 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ (X2 ◇ (v X0))) := by first | exact superpose eq17 eq14 | exact mod_symm (superpose eq17 eq14) | exact superpose eq14 eq17 | exact mod_symm (superpose eq14 eq17)
  have eq40 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X0) ◇ (X3 ◇ X1)) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq46 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = ((e (X0 ◇ X1)) ◇ (e X2)) := by first | exact superpose eq29 eq16 | exact mod_symm (superpose eq29 eq16) | exact superpose eq16 eq29 | exact mod_symm (superpose eq16 eq29)
  have eq47 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq29 eq19 | exact mod_symm (superpose eq29 eq19) | exact superpose eq19 eq29 | exact mod_symm (superpose eq19 eq29)
  have eq49 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq19 eq47 | exact mod_symm (superpose eq19 eq47) | exact superpose eq47 eq19 | exact mod_symm (superpose eq47 eq19)
  have eq50 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = (e ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq16 eq46 | exact mod_symm (superpose eq16 eq46) | exact superpose eq46 eq16 | exact mod_symm (superpose eq46 eq16)
  have eq57 (X0 X1 : G) : (e (X0 ◇ X1)) = (v ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by first | exact superpose eq14 eq21 | exact mod_symm (superpose eq14 eq21) | exact superpose eq21 eq14 | exact mod_symm (superpose eq21 eq14)
  have eq58 (X0 X1 : G) : (v (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq21 eq17 | exact mod_symm (superpose eq21 eq17) | exact superpose eq17 eq21 | exact mod_symm (superpose eq17 eq21)
  have eq59 (X0 X1 : G) : (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq21 eq17 | exact mod_symm (superpose eq21 eq17) | exact superpose eq17 eq21 | exact mod_symm (superpose eq17 eq21)
  have eq60 (X0 X1 : G) : (e (X0 ◇ X1)) = (v ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by first | exact superpose eq41 eq57 | exact mod_symm (superpose eq41 eq57) | exact superpose eq57 eq41 | exact mod_symm (superpose eq57 eq41)
  have eq64 (X0 X1 : G) : (e (X0 ◇ X1)) = (v (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) := by first | exact superpose eq41 eq60 | exact mod_symm (superpose eq41 eq60) | exact superpose eq60 eq41 | exact mod_symm (superpose eq60 eq41)
  have eq82 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq30 eq19 | exact mod_symm (superpose eq30 eq19) | exact superpose eq19 eq30 | exact mod_symm (superpose eq19 eq30)
  have eq84 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq19 eq82 | exact mod_symm (superpose eq19 eq82) | exact superpose eq82 eq19 | exact mod_symm (superpose eq82 eq19)
  have eq93 (X0 X1 : G) : (w (e X0) X1) = (e (v (((e (X0 ◇ X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq16 eq22 | exact mod_symm (superpose eq16 eq22) | exact superpose eq22 eq16 | exact mod_symm (superpose eq22 eq16)
  have eq99 (X0 X1 X2 : G) : (w X1 (X2 ◇ X0)) = (e (v (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2)))) := by first | exact superpose eq14 eq22 | exact mod_symm (superpose eq14 eq22) | exact superpose eq22 eq14 | exact mod_symm (superpose eq22 eq14)
  have eq612 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ (e X1))))) = (e (v (X2 ◇ (e (X0 ◇ X1))))) := by first | exact superpose eq29 eq49 | exact mod_symm (superpose eq29 eq49) | exact superpose eq49 eq29 | exact mod_symm (superpose eq49 eq29)
  have eq613 (X0 X1 X2 : G) : (e (v (X2 ◇ (e (X0 ◇ X1))))) = (e (v (X2 ◇ ((e X0) ◇ X1)))) := by first | exact superpose eq30 eq49 | exact mod_symm (superpose eq30 eq49) | exact superpose eq49 eq30 | exact mod_symm (superpose eq49 eq30)
  have eq619 (X0 X1 : G) : (w X0 (e X1)) = (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq49 eq22 | exact mod_symm (superpose eq49 eq22) | exact superpose eq22 eq49 | exact mod_symm (superpose eq22 eq49)
  have eq626 (X0 X1 X2 : G) : (e (X2 ◇ (v (X0 ◇ (e X1))))) = (e (X2 ◇ (e (v (X0 ◇ X1))))) := by first | exact superpose eq49 eq29 | exact mod_symm (superpose eq49 eq29) | exact superpose eq29 eq49 | exact mod_symm (superpose eq29 eq49)
  have eq629 (X0 X1 X2 : G) : (e (X2 ◇ (v (X0 ◇ (e X1))))) = (e (X2 ◇ (v (X0 ◇ X1)))) := by first | exact superpose eq29 eq626 | exact mod_symm (superpose eq29 eq626) | exact superpose eq626 eq29 | exact mod_symm (superpose eq626 eq29)
  have eq638 (X0 X1 X2 : G) : (e (v (X2 ◇ ((e X0) ◇ X1)))) = (e (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq49 eq613 | exact mod_symm (superpose eq49 eq613) | exact superpose eq613 eq49 | exact mod_symm (superpose eq613 eq49)
  have eq639 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ (e X1))))) = (e (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq49 eq612 | exact mod_symm (superpose eq49 eq612) | exact superpose eq612 eq49 | exact mod_symm (superpose eq612 eq49)
  have eq752 (X0 X1 X2 : G) : (e (v ((X0 ◇ (e X1)) ◇ X2))) = (e (v ((e (X0 ◇ X1)) ◇ X2))) := by first | exact superpose eq29 eq84 | exact mod_symm (superpose eq29 eq84) | exact superpose eq84 eq29 | exact mod_symm (superpose eq84 eq29)
  have eq753 (X0 X1 X2 : G) : (e (v ((e (X0 ◇ X1)) ◇ X2))) = (e (v (((e X0) ◇ X1) ◇ X2))) := by first | exact superpose eq30 eq84 | exact mod_symm (superpose eq30 eq84) | exact superpose eq84 eq30 | exact mod_symm (superpose eq84 eq30)
  have eq794 (X0 X1 X2 : G) : (e (v (((e X0) ◇ X1) ◇ X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq84 eq753 | exact mod_symm (superpose eq84 eq753) | exact superpose eq753 eq84 | exact mod_symm (superpose eq753 eq84)
  have eq795 (X0 X1 X2 : G) : (e (v ((X0 ◇ (e X1)) ◇ X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq84 eq752 | exact mod_symm (superpose eq84 eq752) | exact superpose eq752 eq84 | exact mod_symm (superpose eq752 eq84)
  have eq804 (X0 X1 X2 : G) : ((v X1) ◇ (v (X2 ◇ X0))) = ((v X2) ◇ (v (X0 ◇ X1))) := by first | exact superpose eq17 eq34 | exact mod_symm (superpose eq17 eq34) | exact superpose eq34 eq17 | exact mod_symm (superpose eq34 eq17)
  have eq805 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (v (X1 ◇ X0))) := by first | exact superpose eq20 eq34 | exact mod_symm (superpose eq20 eq34) | exact superpose eq34 eq20 | exact mod_symm (superpose eq34 eq20)
  have eq806 (X0 X1 X2 X3 : G) : (((v X2) ◇ X0) ◇ (v (X3 ◇ X1))) = ((v X3) ◇ (X0 ◇ (v (X1 ◇ X2)))) := by first | exact superpose eq34 eq34 | exact mod_symm (superpose eq34 eq34) | exact superpose eq34 eq34 | exact mod_symm (superpose eq34 eq34)
  have eq807 (X0 X1 X2 : G) : ((e (v X1)) ◇ (v (X2 ◇ X0))) = ((v X2) ◇ (v (X0 ◇ (e X1)))) := by first | exact superpose eq32 eq34 | exact mod_symm (superpose eq32 eq34) | exact superpose eq34 eq32 | exact mod_symm (superpose eq34 eq32)
  have eq809 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = ((v X3) ◇ (X0 ◇ (X1 ◇ (v X2)))) := by first | exact superpose eq14 eq34 | exact mod_symm (superpose eq14 eq34) | exact superpose eq34 eq14 | exact mod_symm (superpose eq34 eq14)
  have eq836 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e X1)))) = ((e (v X1)) ◇ (v (X2 ◇ X0))) := by first | exact superpose eq17 eq807 | exact mod_symm (superpose eq17 eq807) | exact superpose eq807 eq17 | exact mod_symm (superpose eq807 eq17)
  have eq837 (X0 X1 X2 X3 : G) : (((v X2) ◇ X0) ◇ (v (X3 ◇ X1))) = (X0 ◇ (v ((X1 ◇ X2) ◇ X3))) := by first | exact superpose eq39 eq806 | exact mod_symm (superpose eq39 eq806) | exact superpose eq806 eq39 | exact mod_symm (superpose eq806 eq39)
  have eq838 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (((v X0) ◇ (v (X0 ◇ X0))) ◇ (v (X1 ◇ X0))) := by first | exact superpose eq34 eq805 | exact mod_symm (superpose eq34 eq805) | exact superpose eq805 eq34 | exact mod_symm (superpose eq805 eq34)
  have eq839 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ X1))) = ((v X1) ◇ (v (X2 ◇ X0))) := by first | exact superpose eq17 eq804 | exact mod_symm (superpose eq17 eq804) | exact superpose eq804 eq17 | exact mod_symm (superpose eq804 eq17)
  have eq852 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e X1)))) = (v ((e X1) ◇ (X2 ◇ X0))) := by first | exact superpose eq31 eq836 | exact mod_symm (superpose eq31 eq836) | exact superpose eq836 eq31 | exact mod_symm (superpose eq836 eq31)
  have eq853 (X0 X1 : G) : ((v X1) ◇ (e X0)) = ((v (X0 ◇ X0)) ◇ (v ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq837 eq838 | exact mod_symm (superpose eq837 eq838) | exact superpose eq838 eq837 | exact mod_symm (superpose eq838 eq837)
  have eq854 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ X1))) = (v (X1 ◇ (X2 ◇ X0))) := by first | exact superpose eq17 eq839 | exact mod_symm (superpose eq17 eq839) | exact superpose eq839 eq17 | exact mod_symm (superpose eq839 eq17)
  have eq865 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq17 eq853 | exact mod_symm (superpose eq17 eq853) | exact superpose eq853 eq17 | exact mod_symm (superpose eq853 eq17)
  have eq873 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := by first | exact superpose eq41 eq865 | exact mod_symm (superpose eq41 eq865) | exact superpose eq865 eq41 | exact mod_symm (superpose eq865 eq41)
  have eq879 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := by first | exact superpose eq854 eq873 | exact mod_symm (superpose eq854 eq873) | exact superpose eq873 eq854 | exact mod_symm (superpose eq873 eq854)
  have eq885 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by first | exact superpose eq41 eq879 | exact mod_symm (superpose eq41 eq879) | exact superpose eq879 eq41 | exact mod_symm (superpose eq879 eq41)
  have eq1062 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (v (X1 ◇ X2)))) = ((v X2) ◇ ((X0 ◇ (v X1)) ◇ X3)) := by first | exact superpose eq39 eq14 | exact mod_symm (superpose eq39 eq14) | exact superpose eq14 eq39 | exact mod_symm (superpose eq14 eq39)
  have eq1166 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X4 ◇ X2))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq1186 (X0 X1 X2 : G) : ((v X0) ◇ ((((v X0) ◇ ((v X0) ◇ (v X0))) ◇ X1) ◇ X2)) = (X2 ◇ (X1 ◇ (e X0))) := by first | exact superpose eq20 eq35 | exact mod_symm (superpose eq20 eq35) | exact superpose eq35 eq20 | exact mod_symm (superpose eq35 eq20)
  have eq1187 (X0 X1 X2 X3 X4 : G) : ((v X1) ◇ ((((v X2) ◇ X0) ◇ X3) ◇ X4)) = (X4 ◇ (X3 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq34 eq35 | exact mod_symm (superpose eq34 eq35) | exact superpose eq35 eq34 | exact mod_symm (superpose eq35 eq34)
  have eq1188 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X0 ◇ (v (X1 ◇ X2))))) = ((v X2) ◇ (((X0 ◇ (v X1)) ◇ X3) ◇ X4)) := by first | exact superpose eq39 eq35 | exact mod_symm (superpose eq39 eq35) | exact superpose eq35 eq39 | exact mod_symm (superpose eq35 eq39)
  have eq1229 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X1) ◇ X0) ◇ (v (X4 ◇ X2))) = ((v X4) ◇ (X0 ◇ (X1 ◇ ((v X2) ◇ X3)))) := by first | exact superpose eq35 eq34 | exact mod_symm (superpose eq35 eq34) | exact superpose eq34 eq35 | exact mod_symm (superpose eq34 eq35)
  have eq1231 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := by first | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14) | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35)
  have eq1249 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ (e X3))))) := by first | exact superpose eq35 eq84 | exact mod_symm (superpose eq35 eq84) | exact superpose eq84 eq35 | exact mod_symm (superpose eq84 eq35)
  have eq1252 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (v (X3 ◇ X2))) = (X0 ◇ ((X1 ◇ (v X2)) ◇ (v X3))) := by first | exact superpose eq35 eq34 | exact mod_symm (superpose eq35 eq34) | exact superpose eq34 eq35 | exact mod_symm (superpose eq34 eq35)
  have eq1259 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by first | exact superpose eq639 eq1249 | exact mod_symm (superpose eq639 eq1249) | exact superpose eq1249 eq639 | exact mod_symm (superpose eq1249 eq639)
  have eq1294 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = (X2 ◇ (X1 ◇ (((v X0) ◇ (v X0)) ◇ (v (X0 ◇ X0))))) := by first | exact superpose eq1187 eq1186 | exact mod_symm (superpose eq1187 eq1186) | exact superpose eq1186 eq1187 | exact mod_symm (superpose eq1186 eq1187)
  have eq1301 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ ((X1 ◇ (X4 ◇ X2)) ◇ X3)) := by first | exact superpose eq1231 eq1166 | exact mod_symm (superpose eq1231 eq1166) | exact superpose eq1166 eq1231 | exact mod_symm (superpose eq1166 eq1231)
  have eq1350 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = (X2 ◇ ((X1 ◇ (v X0)) ◇ (v ((X0 ◇ X0) ◇ X0)))) := by first | exact superpose eq1252 eq1294 | exact mod_symm (superpose eq1252 eq1294) | exact superpose eq1294 eq1252 | exact mod_symm (superpose eq1294 eq1252)
  have eq1393 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X2 ◇ X1) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0))) := by first | exact superpose eq1252 eq1350 | exact mod_symm (superpose eq1252 eq1350) | exact superpose eq1350 eq1252 | exact mod_symm (superpose eq1350 eq1252)
  have eq1951 (X0 X1 X2 X3 X4 : G) : (((v X2) ◇ X0) ◇ ((X4 ◇ (v X1)) ◇ X3)) = (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) := by first | exact superpose eq34 eq36 | exact mod_symm (superpose eq34 eq36) | exact superpose eq36 eq34 | exact mod_symm (superpose eq36 eq34)
  have eq2070 (X0 X1 X2 X3 : G) : (e (v (X3 ◇ ((X1 ◇ X2) ◇ X0)))) = (e (v (X0 ◇ (X1 ◇ (X2 ◇ (e X3)))))) := by first | exact superpose eq36 eq84 | exact mod_symm (superpose eq36 eq84) | exact superpose eq84 eq36 | exact mod_symm (superpose eq84 eq36)
  have eq2152 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = ((v X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ (v X1)))) := by first | exact superpose eq1231 eq1951 | exact mod_symm (superpose eq1231 eq1951) | exact superpose eq1951 eq1231 | exact mod_symm (superpose eq1951 eq1231)
  have eq2212 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (v (X1 ◇ X2))))) = (((X0 ◇ X3) ◇ X4) ◇ (v (X2 ◇ X1))) := by first | exact superpose eq809 eq2152 | exact mod_symm (superpose eq809 eq2152) | exact superpose eq2152 eq809 | exact mod_symm (superpose eq2152 eq809)
  have eq2607 (X0 X1 X2 X3 X4 : G) : (v (X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = (v ((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X3))) := by first | exact superpose eq35 eq854 | exact mod_symm (superpose eq35 eq854) | exact superpose eq854 eq35 | exact mod_symm (superpose eq854 eq35)
  have eq2625 (X0 X1 X2 X3 : G) : (v (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (v (X0 ◇ (X2 ◇ (X3 ◇ X1)))) := by first | exact superpose eq35 eq854 | exact mod_symm (superpose eq35 eq854) | exact superpose eq854 eq35 | exact mod_symm (superpose eq854 eq35)
  have eq2637 (X0 X1 X2 X3 X4 : G) : (v (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (v (X2 ◇ (((X3 ◇ X1) ◇ X0) ◇ X4))) := by first | exact superpose eq35 eq854 | exact mod_symm (superpose eq35 eq854) | exact superpose eq854 eq35 | exact mod_symm (superpose eq854 eq35)
  have eq2651 (X0 X1 X2 X3 : G) : (v (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (v (X2 ◇ ((X0 ◇ X1) ◇ X3))) := by first | exact superpose eq35 eq854 | exact mod_symm (superpose eq35 eq854) | exact superpose eq854 eq35 | exact mod_symm (superpose eq854 eq35)
  have eq2675 (X0 X1 X2 X3 : G) : (v ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = ((v (X0 ◇ (X1 ◇ X2))) ◇ (v X3)) := by first | exact superpose eq854 eq17 | exact mod_symm (superpose eq854 eq17) | exact superpose eq17 eq854 | exact mod_symm (superpose eq17 eq854)
  have eq2685 (X0 X1 X2 X3 X4 : G) : ((v (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (v X4))) = (X3 ◇ (v (X4 ◇ (X2 ◇ (X0 ◇ X1))))) := by first | exact superpose eq854 eq39 | exact mod_symm (superpose eq854 eq39) | exact superpose eq39 eq854 | exact mod_symm (superpose eq39 eq854)
  have eq2686 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (v (X4 ◇ (X2 ◇ (X0 ◇ X1))))) = (X3 ◇ (v (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by first | exact superpose eq39 eq2685 | exact mod_symm (superpose eq39 eq2685) | exact superpose eq2685 eq39 | exact mod_symm (superpose eq2685 eq39)
  have eq2696 (X0 X1 X2 X3 : G) : (v ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (v ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by first | exact superpose eq17 eq2675 | exact mod_symm (superpose eq17 eq2675) | exact superpose eq2675 eq17 | exact mod_symm (superpose eq2675 eq17)
  have eq2725 (X0 X1 X2 X3 X4 : G) : (v (X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = (v (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X4))) := by first | exact superpose eq1231 eq2607 | exact mod_symm (superpose eq1231 eq2607) | exact superpose eq2607 eq1231 | exact mod_symm (superpose eq2607 eq1231)
  have eq2932 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X3 ◇ X1) ◇ (((X0 ◇ X2) ◇ X4) ◇ X5)) := by first | exact superpose eq40 eq35 | exact mod_symm (superpose eq40 eq35) | exact superpose eq35 eq40 | exact mod_symm (superpose eq35 eq40)
  have eq2947 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X3 ◇ ((X1 ◇ X5) ◇ ((X0 ◇ X2) ◇ X4))) := by first | exact superpose eq1231 eq2932 | exact mod_symm (superpose eq1231 eq2932) | exact superpose eq2932 eq1231 | exact mod_symm (superpose eq2932 eq1231)
  have eq3089 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X3 ◇ (X1 ◇ ((X5 ◇ X4) ◇ (X0 ◇ X2)))) := by first | exact superpose eq1231 eq2947 | exact mod_symm (superpose eq1231 eq2947) | exact superpose eq2947 eq1231 | exact mod_symm (superpose eq2947 eq1231)
  have eq3172 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X3 ◇ (X1 ◇ (X5 ◇ ((X4 ◇ X2) ◇ X0)))) := by first | exact superpose eq1231 eq3089 | exact mod_symm (superpose eq1231 eq3089) | exact superpose eq3089 eq1231 | exact mod_symm (superpose eq3089 eq1231)
  have eq3615 (X0 X1 X2 X3 : G) : (e (v (((X0 ◇ (e X1)) ◇ X2) ◇ X3))) = (e (v ((e ((X0 ◇ X1) ◇ X2)) ◇ X3))) := by first | exact superpose eq50 eq84 | exact mod_symm (superpose eq50 eq84) | exact superpose eq84 eq50 | exact mod_symm (superpose eq84 eq50)
  have eq3616 (X0 X1 X2 X3 : G) : (e (v (((X0 ◇ (e X1)) ◇ X2) ◇ X3))) = (e (v (((X0 ◇ X1) ◇ X2) ◇ X3))) := by first | exact superpose eq84 eq3615 | exact mod_symm (superpose eq84 eq3615) | exact superpose eq3615 eq84 | exact mod_symm (superpose eq3615 eq84)
  have eq3770 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = ((v X0) ◇ (X1 ◇ (X2 ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))))) := by first | exact superpose eq20 eq41 | exact mod_symm (superpose eq20 eq41) | exact superpose eq41 eq20 | exact mod_symm (superpose eq41 eq20)
  have eq3970 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (e X0)) = (((((v X0) ◇ (v X0)) ◇ X2) ◇ X1) ◇ (v (X0 ◇ X0))) := by first | exact superpose eq1229 eq3770 | exact mod_symm (superpose eq1229 eq3770) | exact superpose eq3770 eq1229 | exact mod_symm (superpose eq3770 eq1229)
  have eq4099 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (((v X0) ◇ (v X0)) ◇ (v (X0 ◇ X0))))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq2212 eq3970 | exact mod_symm (superpose eq2212 eq3970) | exact superpose eq3970 eq2212 | exact mod_symm (superpose eq3970 eq2212)
  have eq4169 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (v X0)) ◇ (v ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1252 eq4099 | exact mod_symm (superpose eq1252 eq4099) | exact superpose eq4099 eq1252 | exact mod_symm (superpose eq4099 eq1252)
  have eq4213 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1252 eq4169 | exact mod_symm (superpose eq1252 eq4169) | exact superpose eq4169 eq1252 | exact mod_symm (superpose eq4169 eq1252)
  have eq4244 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (e X0))) = ((X1 ◇ X2) ◇ (e X0)) := by first | exact superpose eq1393 eq4213 | exact mod_symm (superpose eq1393 eq4213) | exact superpose eq4213 eq1393 | exact mod_symm (superpose eq4213 eq1393)
  have eq4506 (X0 X1 X2 : G) : ((v X1) ◇ ((v X0) ◇ (e X2))) = ((v (X0 ◇ X1)) ◇ (e X2)) := by first | exact superpose eq17 eq4244 | exact mod_symm (superpose eq17 eq4244) | exact superpose eq4244 eq17 | exact mod_symm (superpose eq4244 eq17)
  have eq4525 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (X0 ◇ (e X1))) ◇ (e X1)))) := by first | exact superpose eq4244 eq22 | exact mod_symm (superpose eq4244 eq22) | exact superpose eq22 eq4244 | exact mod_symm (superpose eq22 eq4244)
  have eq4532 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ (e X2))))) = (e (v ((X1 ◇ X0) ◇ X2))) := by first | exact superpose eq4244 eq49 | exact mod_symm (superpose eq4244 eq49) | exact superpose eq49 eq4244 | exact mod_symm (superpose eq49 eq4244)
  have eq4565 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ X2)))) = (e (v ((X1 ◇ X0) ◇ X2))) := by first | exact superpose eq639 eq4532 | exact mod_symm (superpose eq639 eq4532) | exact superpose eq4532 eq639 | exact mod_symm (superpose eq4532 eq639)
  have eq4570 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (X0 ◇ (e X1))) ◇ X1))) := by first | exact superpose eq49 eq4525 | exact mod_symm (superpose eq49 eq4525) | exact superpose eq4525 eq49 | exact mod_symm (superpose eq4525 eq49)
  have eq4577 (X0 X1 X2 : G) : ((v (X0 ◇ X1)) ◇ (e X2)) = ((e X2) ◇ (v (X1 ◇ X0))) := by first | exact superpose eq34 eq4506 | exact mod_symm (superpose eq34 eq4506) | exact superpose eq4506 eq34 | exact mod_symm (superpose eq4506 eq34)
  have eq4608 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ (e X1)) ◇ (X0 ◇ X1)))) := by first | exact superpose eq4565 eq4570 | exact mod_symm (superpose eq4565 eq4570) | exact superpose eq4570 eq4565 | exact mod_symm (superpose eq4570 eq4565)
  have eq4636 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by first | exact superpose eq795 eq4608 | exact mod_symm (superpose eq795 eq4608) | exact superpose eq4608 eq795 | exact mod_symm (superpose eq4608 eq795)
  have eq4658 (X0 X1 : G) : (w X0 (e X1)) = (e (v (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by first | exact superpose eq4565 eq4636 | exact mod_symm (superpose eq4565 eq4636) | exact superpose eq4636 eq4565 | exact mod_symm (superpose eq4636 eq4565)
  have eq4753 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((e (X0 ◇ (e X0))) ◇ X1) ◇ X1))) := by first | exact superpose eq30 eq93 | exact mod_symm (superpose eq30 eq93) | exact superpose eq93 eq30 | exact mod_symm (superpose eq93 eq30)
  have eq4755 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e ((X0 ◇ X0) ◇ X1)) ◇ (e X1)))) := by first | exact superpose eq16 eq93 | exact mod_symm (superpose eq16 eq93) | exact superpose eq93 eq16 | exact mod_symm (superpose eq93 eq16)
  have eq4780 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (((e (X0 ◇ X0)) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq93 eq49 | exact mod_symm (superpose eq93 eq49) | exact superpose eq49 eq93 | exact mod_symm (superpose eq49 eq93)
  have eq4802 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq794 eq4780 | exact mod_symm (superpose eq794 eq4780) | exact superpose eq4780 eq794 | exact mod_symm (superpose eq4780 eq794)
  have eq4826 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e ((X0 ◇ X0) ◇ X1)) ◇ X1))) := by first | exact superpose eq49 eq4755 | exact mod_symm (superpose eq49 eq4755) | exact superpose eq4755 eq49 | exact mod_symm (superpose eq4755 eq49)
  have eq4828 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((X0 ◇ (e X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq794 eq4753 | exact mod_symm (superpose eq794 eq4753) | exact superpose eq4753 eq794 | exact mod_symm (superpose eq4753 eq794)
  have eq4850 (X0 X1 : G) : (w X0 (e X1)) = (w (e X0) (e X1)) := by first | exact superpose eq619 eq4802 | exact mod_symm (superpose eq619 eq4802) | exact superpose eq4802 eq619 | exact mod_symm (superpose eq4802 eq619)
  have eq4874 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq84 eq4826 | exact mod_symm (superpose eq84 eq4826) | exact superpose eq4826 eq84 | exact mod_symm (superpose eq4826 eq84)
  have eq4876 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e (e X0)) X1) := by first | exact superpose eq3616 eq4828 | exact mod_symm (superpose eq3616 eq4828) | exact superpose eq4828 eq3616 | exact mod_symm (superpose eq4828 eq3616)
  have eq4917 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w X0 (e X1)) := by first | exact superpose eq4850 eq4874 | exact mod_symm (superpose eq4850 eq4874) | exact superpose eq4874 eq4850 | exact mod_symm (superpose eq4874 eq4850)
  have eq4918 (X0 X1 : G) : (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) = (w (e X0) X1) := by first | exact superpose eq18 eq4876 | exact mod_symm (superpose eq18 eq4876) | exact superpose eq4876 eq18 | exact mod_symm (superpose eq4876 eq18)
  have eq4944 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq22 eq4917 | exact mod_symm (superpose eq22 eq4917) | exact superpose eq4917 eq22 | exact mod_symm (superpose eq4917 eq22)
  have eq4945 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq22 eq4918 | exact mod_symm (superpose eq22 eq4918) | exact superpose eq4918 eq22 | exact mod_symm (superpose eq4918 eq22)
  have eq5461 (X0 X1 X2 : G) : ((v (X2 ◇ X1)) ◇ (e X0)) = (v (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)))) := by first | exact superpose eq40 eq58 | exact mod_symm (superpose eq40 eq58) | exact superpose eq58 eq40 | exact mod_symm (superpose eq58 eq40)
  have eq5466 (X0 X1 : G) : ((v X0) ◇ (e X1)) = (v (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) := by first | exact superpose eq58 eq854 | exact mod_symm (superpose eq58 eq854) | exact superpose eq854 eq58 | exact mod_symm (superpose eq854 eq58)
  have eq5475 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) = ((v X2) ◇ ((v X0) ◇ (e X1))) := by first | exact superpose eq58 eq17 | exact mod_symm (superpose eq58 eq17) | exact superpose eq17 eq58 | exact mod_symm (superpose eq17 eq58)
  have eq5495 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) = ((e X1) ◇ (v (X2 ◇ X0))) := by first | exact superpose eq34 eq5475 | exact mod_symm (superpose eq34 eq5475) | exact superpose eq5475 eq34 | exact mod_symm (superpose eq5475 eq34)
  have eq5503 (X0 X1 : G) : ((v X0) ◇ (e X1)) = (v (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq1301 eq5466 | exact mod_symm (superpose eq1301 eq5466) | exact superpose eq5466 eq1301 | exact mod_symm (superpose eq5466 eq1301)
  have eq5819 (X0 X1 X2 X3 : G) : (v (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3)))))) = ((e X3) ◇ (v (X2 ◇ (X0 ◇ X1)))) := by first | exact superpose eq35 eq59 | exact mod_symm (superpose eq35 eq59) | exact superpose eq59 eq35 | exact mod_symm (superpose eq59 eq35)
  have eq5834 (X0 X1 : G) : (e (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) = (e ((e X0) ◇ (v (e X1)))) := by first | exact superpose eq59 eq49 | exact mod_symm (superpose eq59 eq49) | exact superpose eq49 eq59 | exact mod_symm (superpose eq49 eq59)
  have eq5863 (X0 X1 : G) : (e (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) = (e (X0 ◇ (v (e X1)))) := by first | exact superpose eq30 eq5834 | exact mod_symm (superpose eq30 eq5834) | exact superpose eq5834 eq30 | exact mod_symm (superpose eq5834 eq30)
  have eq5872 (X0 X1 X2 X3 : G) : ((e X3) ◇ (v (X2 ◇ (X0 ◇ X1)))) = ((e X3) ◇ (v (X0 ◇ (X1 ◇ X2)))) := by first | exact superpose eq5495 eq5819 | exact mod_symm (superpose eq5495 eq5819) | exact superpose eq5819 eq5495 | exact mod_symm (superpose eq5819 eq5495)
  have eq5919 (X0 X1 : G) : (e (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) = (e (X0 ◇ (e (v X1)))) := by first | exact superpose eq19 eq5863 | exact mod_symm (superpose eq19 eq5863) | exact superpose eq5863 eq19 | exact mod_symm (superpose eq5863 eq19)
  have eq5966 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) := by first | exact superpose eq29 eq5919 | exact mod_symm (superpose eq29 eq5919) | exact superpose eq5919 eq29 | exact mod_symm (superpose eq5919 eq29)
  have eq6005 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))) := by first | exact superpose eq4565 eq5966 | exact mod_symm (superpose eq4565 eq5966) | exact superpose eq5966 eq4565 | exact mod_symm (superpose eq5966 eq4565)
  have eq6033 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) := by first | exact superpose eq4565 eq6005 | exact mod_symm (superpose eq4565 eq6005) | exact superpose eq6005 eq4565 | exact mod_symm (superpose eq6005 eq4565)
  have eq6055 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := by first | exact superpose eq4565 eq6033 | exact mod_symm (superpose eq4565 eq6033) | exact superpose eq6033 eq4565 | exact mod_symm (superpose eq6033 eq4565)
  have eq6072 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e ((v X1) ◇ (e X0))) := by first | exact superpose eq5503 eq6055 | exact mod_symm (superpose eq5503 eq6055) | exact superpose eq6055 eq5503 | exact mod_symm (superpose eq6055 eq5503)
  have eq6088 (X0 X1 : G) : (e ((v X1) ◇ X0)) = (e (X0 ◇ (v X1))) := by first | exact superpose eq29 eq6072 | exact mod_symm (superpose eq29 eq6072) | exact superpose eq6072 eq29 | exact mod_symm (superpose eq6072 eq29)
  have eq6440 (X0 X1 : G) : (e ((e X0) ◇ X1)) = (e (X1 ◇ (e X0))) := by first | exact superpose eq21 eq6088 | exact mod_symm (superpose eq21 eq6088) | exact superpose eq6088 eq21 | exact mod_symm (superpose eq6088 eq21)
  have eq6540 (X0 X1 : G) : (e ((e X0) ◇ X1)) = (e (X1 ◇ X0)) := by first | exact superpose eq29 eq6440 | exact mod_symm (superpose eq29 eq6440) | exact superpose eq6440 eq29 | exact mod_symm (superpose eq6440 eq29)
  have eq6915 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (((e ((e X0) ◇ X0)) ◇ X1) ◇ X1))) := by first | exact superpose eq6540 eq93 | exact mod_symm (superpose eq6540 eq93) | exact superpose eq93 eq6540 | exact mod_symm (superpose eq93 eq6540)
  have eq6932 (X0 X1 X2 : G) : (e (v (X2 ◇ (e (X0 ◇ X1))))) = (e (v (X2 ◇ ((e X1) ◇ X0)))) := by first | exact superpose eq6540 eq49 | exact mod_symm (superpose eq6540 eq49) | exact superpose eq49 eq6540 | exact mod_symm (superpose eq49 eq6540)
  have eq6945 (X0 X1 X2 : G) : (e (v (X2 ◇ (e (X0 ◇ X1))))) = (e (v (X2 ◇ (X1 ◇ X0)))) := by first | exact superpose eq638 eq6932 | exact mod_symm (superpose eq638 eq6932) | exact superpose eq6932 eq638 | exact mod_symm (superpose eq6932 eq638)
  have eq6960 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v ((((e X0) ◇ X0) ◇ X1) ◇ X1))) := by first | exact superpose eq794 eq6915 | exact mod_symm (superpose eq794 eq6915) | exact superpose eq6915 eq794 | exact mod_symm (superpose eq6915 eq794)
  have eq7001 (X0 X1 X2 : G) : (e (v (X2 ◇ (X0 ◇ X1)))) = (e (v (X2 ◇ (X1 ◇ X0)))) := by first | exact superpose eq49 eq6945 | exact mod_symm (superpose eq49 eq6945) | exact superpose eq6945 eq49 | exact mod_symm (superpose eq6945 eq49)
  have eq7011 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (X1 ◇ (((e X0) ◇ X0) ◇ X1)))) := by first | exact superpose eq4565 eq6960 | exact mod_symm (superpose eq4565 eq6960) | exact superpose eq6960 eq4565 | exact mod_symm (superpose eq6960 eq4565)
  have eq7043 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (X1 ◇ (X0 ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq1259 eq7011 | exact mod_symm (superpose eq1259 eq7011) | exact superpose eq7011 eq1259 | exact mod_symm (superpose eq7011 eq1259)
  have eq7061 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := by first | exact superpose eq2070 eq7043 | exact mod_symm (superpose eq2070 eq7043) | exact superpose eq7043 eq2070 | exact mod_symm (superpose eq7043 eq2070)
  have eq7064 (X0 X1 : G) : (w (e (e X0)) X1) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq7001 eq7061 | exact mod_symm (superpose eq7001 eq7061) | exact superpose eq7061 eq7001 | exact mod_symm (superpose eq7061 eq7001)
  have eq7065 (X0 X1 : G) : (w (e X0) X1) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq4945 eq7064 | exact mod_symm (superpose eq4945 eq7064) | exact superpose eq7064 eq4945 | exact mod_symm (superpose eq7064 eq4945)
  have eq7066 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq4945 eq7065 | exact mod_symm (superpose eq4945 eq7065) | exact superpose eq7065 eq4945 | exact mod_symm (superpose eq7065 eq4945)
  have eq8925 (X0 X1 : G) : (w X1 (e X0)) = (e (v (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (((X1 ◇ X1) ◇ (e X0)) ◇ (v X0))))) := by first | exact superpose eq20 eq99 | exact mod_symm (superpose eq20 eq99) | exact superpose eq99 eq20 | exact mod_symm (superpose eq99 eq20)
  have eq9037 (X0 X1 : G) : (w X1 (e X0)) = (e (v (((v X0) ◇ (v X0)) ◇ ((v X0) ◇ (((X1 ◇ X1) ◇ (e X0)) ◇ (v X0)))))) := by first | exact superpose eq4565 eq8925 | exact mod_symm (superpose eq4565 eq8925) | exact superpose eq8925 eq4565 | exact mod_symm (superpose eq8925 eq4565)
  have eq9116 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (((X1 ◇ X1) ◇ (e X0)) ◇ (v X0))))))) := by first | exact superpose eq4565 eq9037 | exact mod_symm (superpose eq4565 eq9037) | exact superpose eq9037 eq4565 | exact mod_symm (superpose eq9037 eq4565)
  have eq9181 (X0 X1 : G) : (w X1 (e X0)) = (e ((v ((X1 ◇ X1) ◇ (e X0))) ◇ (e (v X0)))) := by first | exact superpose eq885 eq9116 | exact mod_symm (superpose eq885 eq9116) | exact superpose eq9116 eq885 | exact mod_symm (superpose eq9116 eq885)
  have eq9230 (X0 X1 : G) : (w X1 (e X0)) = (e ((v ((X1 ◇ X1) ◇ (e X0))) ◇ (v X0))) := by first | exact superpose eq29 eq9181 | exact mod_symm (superpose eq29 eq9181) | exact superpose eq9181 eq29 | exact mod_symm (superpose eq9181 eq29)
  have eq9266 (X0 X1 : G) : (w X1 (e X0)) = (e ((v X0) ◇ (v ((X1 ◇ X1) ◇ (e X0))))) := by first | exact superpose eq6088 eq9230 | exact mod_symm (superpose eq6088 eq9230) | exact superpose eq9230 eq6088 | exact mod_symm (superpose eq9230 eq6088)
  have eq9292 (X0 X1 : G) : (w X1 (e X0)) = (e ((v X0) ◇ (v ((X1 ◇ X1) ◇ X0)))) := by first | exact superpose eq629 eq9266 | exact mod_symm (superpose eq629 eq9266) | exact superpose eq9266 eq629 | exact mod_symm (superpose eq9266 eq629)
  have eq9311 (X0 X1 : G) : (w X1 (e X0)) = (e (v (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by first | exact superpose eq17 eq9292 | exact mod_symm (superpose eq17 eq9292) | exact superpose eq9292 eq17 | exact mod_symm (superpose eq9292 eq17)
  have eq9323 (X0 X1 : G) : (w X1 (e X0)) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq1259 eq9311 | exact mod_symm (superpose eq1259 eq9311) | exact superpose eq9311 eq1259 | exact mod_symm (superpose eq9311 eq1259)
  have eq9332 (X0 X1 : G) : (w X0 X1) = (w X1 (e X0)) := by first | exact superpose eq7066 eq9323 | exact mod_symm (superpose eq7066 eq9323) | exact superpose eq9323 eq7066 | exact mod_symm (superpose eq9323 eq7066)
  have eq9386 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq9332 eq4944 | exact mod_symm (superpose eq9332 eq4944) | exact superpose eq4944 eq9332 | exact mod_symm (superpose eq4944 eq9332)
  have eq10234 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0)))))))) := by first | exact superpose eq20 eq64 | exact mod_symm (superpose eq20 eq64) | exact superpose eq64 eq20 | exact mod_symm (superpose eq64 eq20)
  have eq10357 (X0 : G) : (e (e X0)) = ((v ((((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0)))) ◇ (v X0))) ◇ (e (v X0))) := by first | exact superpose eq5461 eq10234 | exact mod_symm (superpose eq5461 eq10234) | exact superpose eq10234 eq5461 | exact mod_symm (superpose eq10234 eq5461)
  have eq10423 (X0 : G) : (e (e X0)) = (v (((((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0)))) ◇ (v X0)) ◇ (e X0))) := by first | exact superpose eq32 eq10357 | exact mod_symm (superpose eq32 eq10357) | exact superpose eq10357 eq32 | exact mod_symm (superpose eq10357 eq32)
  have eq10489 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ ((((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0)))) ◇ (e X0)))) := by first | exact superpose eq4244 eq10423 | exact mod_symm (superpose eq4244 eq10423) | exact superpose eq10423 eq4244 | exact mod_symm (superpose eq10423 eq4244)
  have eq10551 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v X0) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (e X0))))))) := by first | exact superpose eq852 eq10489 | exact mod_symm (superpose eq852 eq10489) | exact superpose eq10489 eq852 | exact mod_symm (superpose eq10489 eq852)
  have eq10609 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((v X0) ◇ ((e X0) ◇ (((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))))))) := by first | exact superpose eq3172 eq10551 | exact mod_symm (superpose eq3172 eq10551) | exact superpose eq10551 eq3172 | exact mod_symm (superpose eq10551 eq3172)
  have eq10659 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((e X0) ◇ ((((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ (v X0))))) := by first | exact superpose eq2625 eq10609 | exact mod_symm (superpose eq2625 eq10609) | exact superpose eq10609 eq2625 | exact mod_symm (superpose eq10609 eq2625)
  have eq10703 (X0 : G) : (e (e X0)) = (v (((((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ (v X0)) ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq33 eq10659 | exact mod_symm (superpose eq33 eq10659) | exact superpose eq10659 eq33 | exact mod_symm (superpose eq10659 eq33)
  have eq10745 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ ((((v X0) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq4244 eq10703 | exact mod_symm (superpose eq4244 eq10703) | exact superpose eq10703 eq4244 | exact mod_symm (superpose eq10703 eq4244)
  have eq10784 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (v (X0 ◇ X0)))))) := by first | exact superpose eq1187 eq10745 | exact mod_symm (superpose eq1187 eq10745) | exact superpose eq10745 eq1187 | exact mod_symm (superpose eq10745 eq1187)
  have eq10822 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ ((v (X0 ◇ X0)) ◇ ((v X0) ◇ ((v X0) ◇ (v X0))))))) := by first | exact superpose eq2625 eq10784 | exact mod_symm (superpose eq2625 eq10784) | exact superpose eq10784 eq2625 | exact mod_symm (superpose eq10784 eq2625)
  have eq10857 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ (((((v X0) ◇ (v X0)) ◇ (v (X0 ◇ X0))) ◇ ((v X0) ◇ ((v X0) ◇ (v X0)))) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq2637 eq10822 | exact mod_symm (superpose eq2637 eq10822) | exact superpose eq10822 eq2637 | exact mod_symm (superpose eq10822 eq2637)
  have eq10889 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ ((v X0) ◇ (v X0))) ◇ (((v X0) ◇ (v X0)) ◇ (v ((X0 ◇ X0) ◇ X0)))))) := by first | exact superpose eq1188 eq10857 | exact mod_symm (superpose eq1188 eq10857) | exact superpose eq10857 eq1188 | exact mod_symm (superpose eq10857 eq1188)
  have eq10916 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ (v X0)) ◇ ((v ((X0 ◇ X0) ◇ X0)) ◇ ((v X0) ◇ ((v X0) ◇ (v X0))))))) := by first | exact superpose eq2625 eq10889 | exact mod_symm (superpose eq2625 eq10889) | exact superpose eq10889 eq2625 | exact mod_symm (superpose eq10889 eq2625)
  have eq10937 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ (((((v X0) ◇ (v X0)) ◇ (v ((X0 ◇ X0) ◇ X0))) ◇ ((v X0) ◇ (v X0))) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq2637 eq10916 | exact mod_symm (superpose eq2637 eq10916) | exact superpose eq10916 eq2637 | exact mod_symm (superpose eq10916 eq2637)
  have eq10955 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (((v X0) ◇ (v X0)) ◇ (((v X0) ◇ (v X0)) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0)))))) := by first | exact superpose eq1188 eq10937 | exact mod_symm (superpose eq1188 eq10937) | exact superpose eq10937 eq1188 | exact mod_symm (superpose eq10937 eq1188)
  have eq10972 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ (((((v X0) ◇ (v X0)) ◇ (v X0)) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq2725 eq10955 | exact mod_symm (superpose eq2725 eq10955) | exact superpose eq10955 eq2725 | exact mod_symm (superpose eq10955 eq2725)
  have eq10989 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ ((((v X0) ◇ (v X0)) ◇ (v X0)) ◇ (v ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))))) := by first | exact superpose eq1062 eq10972 | exact mod_symm (superpose eq1062 eq10972) | exact superpose eq10972 eq1062 | exact mod_symm (superpose eq10972 eq1062)
  have eq11006 (X0 : G) : (e (e X0)) = (v ((v X0) ◇ (((e (X0 ◇ X0)) ◇ ((v X0) ◇ (v X0))) ◇ (v ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))))) := by first | exact superpose eq2651 eq10989 | exact mod_symm (superpose eq2651 eq10989) | exact superpose eq10989 eq2651 | exact mod_symm (superpose eq10989 eq2651)
  have eq11022 (X0 : G) : (e (e X0)) = (v (((e (X0 ◇ X0)) ◇ ((v X0) ◇ (v X0))) ◇ (v (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0)))) := by first | exact superpose eq39 eq11006 | exact mod_symm (superpose eq39 eq11006) | exact superpose eq11006 eq39 | exact mod_symm (superpose eq11006 eq39)
  have eq11035 (X0 : G) : (e (e X0)) = (v (((v X0) ◇ ((v X0) ◇ (e (X0 ◇ X0)))) ◇ (v (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0)))) := by first | exact superpose eq2696 eq11022 | exact mod_symm (superpose eq2696 eq11022) | exact superpose eq11022 eq2696 | exact mod_symm (superpose eq11022 eq2696)
  have eq11047 (X0 : G) : (e (e X0)) = (v (((v X0) ◇ (e (X0 ◇ X0))) ◇ (v ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))))) := by first | exact superpose eq837 eq11035 | exact mod_symm (superpose eq837 eq11035) | exact superpose eq11035 eq837 | exact mod_symm (superpose eq11035 eq837)
  have eq11059 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (v ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) := by first | exact superpose eq837 eq11047 | exact mod_symm (superpose eq837 eq11047) | exact superpose eq11047 eq837 | exact mod_symm (superpose eq11047 eq837)
  have eq11070 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (v (X0 ◇ (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0)))))) := by first | exact superpose eq5872 eq11059 | exact mod_symm (superpose eq5872 eq11059) | exact superpose eq11059 eq5872 | exact mod_symm (superpose eq11059 eq5872)
  have eq11079 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ (v (X0 ◇ (X0 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))))))) := by first | exact superpose eq2686 eq11070 | exact mod_symm (superpose eq2686 eq11070) | exact superpose eq11070 eq2686 | exact mod_symm (superpose eq11070 eq2686)
  have eq11087 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ X0)) ◇ ((v (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (e X0)))) := by first | exact superpose eq885 eq11079 | exact mod_symm (superpose eq885 eq11079) | exact superpose eq11079 eq885 | exact mod_symm (superpose eq11079 eq885)
  have eq11091 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((e (X0 ◇ X0)) ◇ (v (((X0 ◇ X0) ◇ X0) ◇ X0))))) := by first | exact superpose eq852 eq11087 | exact mod_symm (superpose eq852 eq11087) | exact superpose eq11087 eq852 | exact mod_symm (superpose eq11087 eq852)
  have eq11094 (X0 : G) : (e (e X0)) = (v ((v (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (e (X0 ◇ (X0 ◇ X0))))) := by first | exact superpose eq33 eq11091 | exact mod_symm (superpose eq33 eq11091) | exact superpose eq11091 eq33 | exact mod_symm (superpose eq11091 eq33)
  have eq11097 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ (X0 ◇ X0))) ◇ (v (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := by first | exact superpose eq4577 eq11094 | exact mod_symm (superpose eq4577 eq11094) | exact superpose eq11094 eq4577 | exact mod_symm (superpose eq11094 eq4577)
  have eq11100 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ (X0 ◇ X0))) ◇ (v (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by first | exact superpose eq5872 eq11097 | exact mod_symm (superpose eq5872 eq11097) | exact superpose eq11097 eq5872 | exact mod_symm (superpose eq11097 eq5872)
  have eq11102 (X0 : G) : (e (e X0)) = (v ((e (X0 ◇ (X0 ◇ X0))) ◇ (e X0))) := by first | exact superpose eq21 eq11100 | exact mod_symm (superpose eq21 eq11100) | exact superpose eq11100 eq21 | exact mod_symm (superpose eq11100 eq21)
  have eq11104 (X0 : G) : (e (e X0)) = (v (e ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := by first | exact superpose eq16 eq11102 | exact mod_symm (superpose eq16 eq11102) | exact superpose eq11102 eq16 | exact mod_symm (superpose eq11102 eq16)
  have eq11105 (X0 : G) : (e (e X0)) = (e (v ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := by first | exact superpose eq19 eq11104 | exact mod_symm (superpose eq19 eq11104) | exact superpose eq11104 eq19 | exact mod_symm (superpose eq11104 eq19)
  have eq11106 (X0 : G) : (e (e X0)) = (e (v ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by first | exact superpose eq4565 eq11105 | exact mod_symm (superpose eq4565 eq11105) | exact superpose eq11105 eq4565 | exact mod_symm (superpose eq11105 eq4565)
  have eq11107 (X0 : G) : (e (e X0)) = (e (v (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by first | exact superpose eq4565 eq11106 | exact mod_symm (superpose eq4565 eq11106) | exact superpose eq11106 eq4565 | exact mod_symm (superpose eq11106 eq4565)
  have eq11108 (X0 : G) : (e (e X0)) = (w X0 (e X0)) := by first | exact superpose eq4658 eq11107 | exact mod_symm (superpose eq4658 eq11107) | exact superpose eq11107 eq4658 | exact mod_symm (superpose eq11107 eq4658)
  have eq11109 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq4944 eq11108 | exact mod_symm (superpose eq4944 eq11108) | exact superpose eq11108 eq4944 | exact mod_symm (superpose eq11108 eq4944)
  have eq11110 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq18 eq11109 | exact mod_symm (superpose eq18 eq11109) | exact superpose eq11109 eq18 | exact mod_symm (superpose eq11109 eq18)
  have eq11130 : (w x (w y y)) ≠ (w y (e x)) := by first | exact superpose eq11110 eq23 | exact mod_symm (superpose eq11110 eq23) | exact superpose eq23 eq11110 | exact mod_symm (superpose eq23 eq11110)
  have eq11131 : (w x (w y y)) ≠ (w y x) := by first | exact superpose eq4944 eq11130 | exact mod_symm (superpose eq4944 eq11130) | exact superpose eq11130 eq4944 | exact mod_symm (superpose eq11130 eq4944)
  have eq11150 : (w x (w y y)) ≠ (w x y) := by first | exact superpose eq9386 eq11131 | exact mod_symm (superpose eq9386 eq11131) | exact superpose eq11131 eq9386 | exact mod_symm (superpose eq11131 eq9386)
  have eq11164 : (w x y) ≠ (w x (e y)) := by first | exact superpose eq11110 eq11150 | exact mod_symm (superpose eq11110 eq11150) | exact superpose eq11150 eq11110 | exact mod_symm (superpose eq11150 eq11110)
  subsumption eq11164 eq4944


/-- Equation 4541 `x ◇ (y ◇ z) = (z ◇ x) ◇ y` is term-definable from equation 4364 over finite magmas, via the term
`x □ y := (x ◇ y)` with `u a = (a ◇ (a ◇ a))`
taken at u^[1N+1]. -/
private theorem aux4364_4541 [Magma G] (h : Equation4364 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huh : ∀ a b : G, ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ b))) = (a ◇ (a ◇ a)) ◇ (b ◇ (b ◇ b)))
    (huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a)
    (hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a)
    (hw : ∀ a b : G, w a b = (e ((a ◇ b))))
    (x y z : G) :
    (w x (w y z)) =
      (w (w z x) y) := by
  by_contra nh
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have eq16 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq17 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq18 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq19 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq20 (X0 : G) : (e X0) = ((v X0) ◇ ((v X0) ◇ (v X0))) := mod_symm (huv ..)
  have eq21 (X0 : G) : (e X0) = (v (X0 ◇ (X0 ◇ X0))) := mod_symm (hvu ..)
  have eq22 (X0 X1 : G) : (e (X0 ◇ X1)) = (w X0 X1) := mod_symm (hw ..)
  have eq23 : (w x (w y z)) ≠ (w (w z x) y) := mod_symm nh
  have eq24 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (w X0 X1) := by first | exact superpose eq22 eq16 | exact mod_symm (superpose eq22 eq16) | exact superpose eq16 eq22 | exact mod_symm (superpose eq16 eq22)
  have eq28 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (v (w X0 X1)) := by first | exact superpose eq22 eq19 | exact mod_symm (superpose eq22 eq19) | exact superpose eq19 eq22 | exact mod_symm (superpose eq19 eq22)
  have eq29 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq22 eq18 | exact mod_symm (superpose eq22 eq18) | exact superpose eq18 eq22 | exact mod_symm (superpose eq18 eq22)
  have eq32 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (w (e X0) X1) := by first | exact superpose eq18 eq24 | exact mod_symm (superpose eq18 eq24) | exact superpose eq24 eq18 | exact mod_symm (superpose eq24 eq18)
  have eq33 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = ((w X0 X1) ◇ (e X2)) := by first | exact superpose eq22 eq24 | exact mod_symm (superpose eq22 eq24) | exact superpose eq24 eq22 | exact mod_symm (superpose eq24 eq22)
  have eq35 (X0 X1 : G) : (w X1 (e X0)) = ((e X1) ◇ (e X0)) := by first | exact superpose eq18 eq24 | exact mod_symm (superpose eq18 eq24) | exact superpose eq24 eq18 | exact mod_symm (superpose eq24 eq18)
  have eq36 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = ((e X2) ◇ (w X0 X1)) := by first | exact superpose eq22 eq24 | exact mod_symm (superpose eq22 eq24) | exact superpose eq24 eq22 | exact mod_symm (superpose eq24 eq22)
  have eq37 (X0 X1 X2 : G) : ((e X2) ◇ (w X0 X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq29 eq24 | exact mod_symm (superpose eq29 eq24) | exact superpose eq24 eq29 | exact mod_symm (superpose eq24 eq29)
  have eq42 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq24 eq35 | exact mod_symm (superpose eq24 eq35) | exact superpose eq35 eq24 | exact mod_symm (superpose eq35 eq24)
  have eq43 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq24 eq32 | exact mod_symm (superpose eq24 eq32) | exact superpose eq32 eq24 | exact mod_symm (superpose eq32 eq24)
  have eq49 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (w (v X0) (v X1)) := by first | exact superpose eq17 eq22 | exact mod_symm (superpose eq17 eq22) | exact superpose eq22 eq17 | exact mod_symm (superpose eq22 eq17)
  have eq52 (X0 X1 : G) : (v (w X0 X1)) = (w (v X0) (v X1)) := by first | exact superpose eq28 eq49 | exact mod_symm (superpose eq28 eq49) | exact superpose eq49 eq28 | exact mod_symm (superpose eq49 eq28)
  have eq54 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq22 eq42 | exact mod_symm (superpose eq22 eq42) | exact superpose eq42 eq22 | exact mod_symm (superpose eq42 eq22)
  have eq56 (X0 X1 X2 : G) : ((e X0) ◇ ((e X1) ◇ X2)) = (X2 ◇ (w X0 X1)) := by first | exact superpose eq24 eq14 | exact mod_symm (superpose eq24 eq14) | exact superpose eq14 eq24 | exact mod_symm (superpose eq14 eq24)
  have eq58 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (w X0 X1)) = ((e X1) ◇ (X2 ◇ (e X0))) := by first | exact superpose eq24 eq14 | exact mod_symm (superpose eq24 eq14) | exact superpose eq14 eq24 | exact mod_symm (superpose eq14 eq24)
  have eq64 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by first | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14) | exact superpose eq14 eq14 | exact mod_symm (superpose eq14 eq14)
  have eq68 (X0 X1 X2 : G) : (e (X0 ◇ (X1 ◇ X2))) = (w X1 (X2 ◇ X0)) := by first | exact superpose eq14 eq22 | exact mod_symm (superpose eq14 eq22) | exact superpose eq22 eq14 | exact mod_symm (superpose eq22 eq14)
  have eq69 (X0 X1 : G) : (e (X1 ◇ X0)) = (v ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := by first | exact superpose eq14 eq21 | exact mod_symm (superpose eq14 eq21) | exact superpose eq21 eq14 | exact mod_symm (superpose eq21 eq14)
  have eq70 (X0 X1 : G) : (e (X1 ◇ X0)) = (v (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)))) := by first | exact superpose eq14 eq69 | exact mod_symm (superpose eq14 eq69) | exact superpose eq69 eq14 | exact mod_symm (superpose eq69 eq14)
  have eq71 (X0 X1 X2 : G) : (w X0 (X1 ◇ X2)) = (w X1 (X2 ◇ X0)) := by first | exact superpose eq22 eq68 | exact mod_symm (superpose eq22 eq68) | exact superpose eq68 eq22 | exact mod_symm (superpose eq68 eq22)
  have eq74 (X0 X1 : G) : (e (X1 ◇ X0)) = (v (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by first | exact superpose eq64 eq70 | exact mod_symm (superpose eq64 eq70) | exact superpose eq70 eq64 | exact mod_symm (superpose eq70 eq64)
  have eq76 (X0 X1 : G) : (e (X1 ◇ X0)) = (v (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))) := by first | exact superpose eq64 eq74 | exact mod_symm (superpose eq64 eq74) | exact superpose eq74 eq64 | exact mod_symm (superpose eq74 eq64)
  have eq78 (X0 X1 : G) : (w X1 X0) = (v (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))) := by first | exact superpose eq22 eq76 | exact mod_symm (superpose eq22 eq76) | exact superpose eq76 eq22 | exact mod_symm (superpose eq76 eq22)
  have eq80 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = (w (w X0 X1) X2) := by first | exact superpose eq22 eq43 | exact mod_symm (superpose eq22 eq43) | exact superpose eq43 eq22 | exact mod_symm (superpose eq43 eq22)
  have eq92 (X0 : G) : (e (e X0)) = (w (v X0) ((v X0) ◇ (v X0))) := by first | exact superpose eq20 eq22 | exact mod_symm (superpose eq20 eq22) | exact superpose eq22 eq20 | exact mod_symm (superpose eq22 eq20)
  have eq93 (X0 : G) : (e (e X0)) = (w (v X0) (v (X0 ◇ X0))) := by first | exact superpose eq17 eq92 | exact mod_symm (superpose eq17 eq92) | exact superpose eq92 eq17 | exact mod_symm (superpose eq92 eq17)
  have eq99 (X0 : G) : (e (e X0)) = (v (w X0 (X0 ◇ X0))) := by first | exact superpose eq52 eq93 | exact mod_symm (superpose eq52 eq93) | exact superpose eq93 eq52 | exact mod_symm (superpose eq93 eq52)
  have eq104 (X0 : G) : (e X0) = (v (w X0 (X0 ◇ X0))) := by first | exact superpose eq18 eq99 | exact mod_symm (superpose eq18 eq99) | exact superpose eq99 eq18 | exact mod_symm (superpose eq99 eq18)
  have eq407 (X0 X1 X2 : G) : (e (v (X0 ◇ (X1 ◇ X2)))) = (v (w X2 (X0 ◇ X1))) := by first | exact superpose eq14 eq28 | exact mod_symm (superpose eq14 eq28) | exact superpose eq28 eq14 | exact mod_symm (superpose eq28 eq14)
  have eq430 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ X1))) = (v (w X0 (X1 ◇ X2))) := by first | exact superpose eq28 eq407 | exact mod_symm (superpose eq28 eq407) | exact superpose eq407 eq28 | exact mod_symm (superpose eq407 eq28)
  have eq493 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w (e X1) (X2 ◇ (e X0))) := by first | exact superpose eq24 eq71 | exact mod_symm (superpose eq24 eq71) | exact superpose eq71 eq24 | exact mod_symm (superpose eq71 eq24)
  have eq509 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w X1 (X2 ◇ (e X0))) := by first | exact superpose eq43 eq493 | exact mod_symm (superpose eq43 eq493) | exact superpose eq493 eq43 | exact mod_symm (superpose eq493 eq43)
  have eq519 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X1 (X2 ◇ (e X0))) := by first | exact superpose eq54 eq509 | exact mod_symm (superpose eq54 eq509) | exact superpose eq509 eq54 | exact mod_symm (superpose eq509 eq54)
  have eq583 (X0 X1 X2 X3 : G) : (w (X2 ◇ X3) (X0 ◇ X1)) = ((w X2 X3) ◇ (w X0 X1)) := by first | exact superpose eq22 eq33 | exact mod_symm (superpose eq22 eq33) | exact superpose eq33 eq22 | exact mod_symm (superpose eq33 eq22)
  have eq590 (X0 X1 X2 X3 : G) : (X3 ◇ (w (X0 ◇ X1) X2)) = ((e X2) ◇ (X3 ◇ (w X0 X1))) := by first | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14) | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33)
  have eq629 (X0 X1 X2 X3 : G) : (w X3 (X2 ◇ (X0 ◇ X1))) = (w X3 (w X0 (X1 ◇ X2))) := by first | exact superpose eq71 eq54 | exact mod_symm (superpose eq71 eq54) | exact superpose eq54 eq71 | exact mod_symm (superpose eq54 eq71)
  have eq649 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ X2))) = (w X3 (X2 ◇ (X0 ◇ X1))) := by first | exact superpose eq54 eq629 | exact mod_symm (superpose eq54 eq629) | exact superpose eq629 eq54 | exact mod_symm (superpose eq629 eq54)
  have eq720 (X0 X1 X2 X3 : G) : (w X3 (w (X0 ◇ X1) X2)) = (w X3 ((w X0 X1) ◇ X2)) := by first | exact superpose eq80 eq54 | exact mod_symm (superpose eq80 eq54) | exact superpose eq54 eq80 | exact mod_symm (superpose eq54 eq80)
  have eq726 (X0 X1 X2 X3 : G) : (w (X0 ◇ X1) (X2 ◇ X3)) = (w X3 ((w X0 X1) ◇ X2)) := by first | exact superpose eq80 eq71 | exact mod_symm (superpose eq80 eq71) | exact superpose eq71 eq80 | exact mod_symm (superpose eq71 eq80)
  have eq735 (X0 X1 X2 X3 : G) : ((w X0 X1) ◇ (w X2 X3)) = (w X3 ((w X0 X1) ◇ X2)) := by first | exact superpose eq583 eq726 | exact mod_symm (superpose eq583 eq726) | exact superpose eq726 eq583 | exact mod_symm (superpose eq726 eq583)
  have eq739 (X0 X1 X2 X3 : G) : (w X3 ((X0 ◇ X1) ◇ X2)) = (w X3 ((w X0 X1) ◇ X2)) := by first | exact superpose eq54 eq720 | exact mod_symm (superpose eq54 eq720) | exact superpose eq720 eq54 | exact mod_symm (superpose eq720 eq54)
  have eq759 (X0 X1 X2 X3 : G) : (w X3 ((X0 ◇ X1) ◇ X2)) = ((w X0 X1) ◇ (w X2 X3)) := by first | exact superpose eq735 eq739 | exact mod_symm (superpose eq735 eq739) | exact superpose eq739 eq735 | exact mod_symm (superpose eq739 eq735)
  have eq967 (X0 X1 X2 X3 : G) : ((e X3) ◇ (w X0 (X1 ◇ X2))) = ((w X1 X2) ◇ (w X3 X0)) := by first | exact superpose eq36 eq56 | exact mod_symm (superpose eq36 eq56) | exact superpose eq56 eq36 | exact mod_symm (superpose eq56 eq36)
  have eq968 (X0 X1 X2 X3 : G) : (((e X2) ◇ X0) ◇ (w X3 X1)) = ((e X3) ◇ (X0 ◇ (w X1 X2))) := by first | exact superpose eq56 eq56 | exact mod_symm (superpose eq56 eq56) | exact superpose eq56 eq56 | exact mod_symm (superpose eq56 eq56)
  have eq994 (X0 X1 X2 X3 : G) : (((e X2) ◇ X0) ◇ (w X3 X1)) = (X0 ◇ (w (X1 ◇ X2) X3)) := by first | exact superpose eq590 eq968 | exact mod_symm (superpose eq590 eq968) | exact superpose eq968 eq590 | exact mod_symm (superpose eq968 eq590)
  have eq995 (X0 X1 X2 X3 : G) : (w X3 (w X0 (X1 ◇ X2))) = ((w X1 X2) ◇ (w X3 X0)) := by first | exact superpose eq37 eq967 | exact mod_symm (superpose eq37 eq967) | exact superpose eq967 eq37 | exact mod_symm (superpose eq967 eq37)
  have eq1011 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ X2))) = ((w X1 X2) ◇ (w X3 X0)) := by first | exact superpose eq54 eq995 | exact mod_symm (superpose eq54 eq995) | exact superpose eq995 eq54 | exact mod_symm (superpose eq995 eq54)
  have eq1098 (X0 X1 X2 X3 : G) : ((e X3) ◇ (X0 ◇ (w X1 X2))) = ((X0 ◇ (e X1)) ◇ (w X3 X2)) := by first | exact superpose eq61 eq56 | exact mod_symm (superpose eq61 eq56) | exact superpose eq56 eq61 | exact mod_symm (superpose eq56 eq61)
  have eq1119 (X0 X1 X2 X3 : G) : (X0 ◇ (w (X1 ◇ X2) X3)) = ((X0 ◇ (e X1)) ◇ (w X3 X2)) := by first | exact superpose eq590 eq1098 | exact mod_symm (superpose eq590 eq1098) | exact superpose eq1098 eq590 | exact mod_symm (superpose eq1098 eq590)
  have eq1694 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w (e X0) (X1 ◇ X2)) := by first | exact superpose eq24 eq519 | exact mod_symm (superpose eq24 eq519) | exact superpose eq519 eq24 | exact mod_symm (superpose eq519 eq24)
  have eq1738 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w X0 (X1 ◇ X2)) := by first | exact superpose eq43 eq1694 | exact mod_symm (superpose eq43 eq1694) | exact superpose eq1694 eq43 | exact mod_symm (superpose eq1694 eq43)
  have eq1915 (X0 X1 X2 : G) : (w X0 (w X1 X2)) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq1738 eq71 | exact mod_symm (superpose eq1738 eq71) | exact superpose eq71 eq1738 | exact mod_symm (superpose eq71 eq1738)
  have eq2174 (X0 X1 X2 X3 : G) : (v (w X3 (X2 ◇ (X0 ◇ X1)))) = (e (v (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by first | exact superpose eq58 eq28 | exact mod_symm (superpose eq58 eq28) | exact superpose eq28 eq58 | exact mod_symm (superpose eq28 eq58)
  have eq2199 (X0 X1 X2 X3 : G) : (v (w X3 (X2 ◇ (X0 ◇ X1)))) = (v (w X0 ((X1 ◇ X2) ◇ X3))) := by first | exact superpose eq28 eq2174 | exact mod_symm (superpose eq28 eq2174) | exact superpose eq2174 eq28 | exact mod_symm (superpose eq2174 eq28)
  have eq2287 (X0 X1 X2 X3 : G) : (v (w X3 (X2 ◇ (X0 ◇ X1)))) = (v ((w X1 X2) ◇ (w X3 X0))) := by first | exact superpose eq759 eq2199 | exact mod_symm (superpose eq759 eq2199) | exact superpose eq2199 eq759 | exact mod_symm (superpose eq2199 eq759)
  have eq2349 (X0 X1 X2 X3 : G) : (v ((w X1 X2) ◇ (w X3 X0))) = (v ((w X0 X1) ◇ (w X3 X2))) := by first | exact superpose eq1011 eq2287 | exact mod_symm (superpose eq1011 eq2287) | exact superpose eq2287 eq1011 | exact mod_symm (superpose eq2287 eq1011)
  have eq2676 (X0 X1 X2 : G) : (w X0 (w X1 X2)) = (w X1 (w X2 X0)) := by first | exact superpose eq1915 eq1738 | exact mod_symm (superpose eq1915 eq1738) | exact superpose eq1738 eq1915 | exact mod_symm (superpose eq1738 eq1915)
  have eq4767 (X0 X1 : G) : (e (X0 ◇ X1)) = (v (w (X0 ◇ X1) (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq64 eq104 | exact mod_symm (superpose eq64 eq104) | exact superpose eq104 eq64 | exact mod_symm (superpose eq104 eq64)
  have eq4808 (X0 X1 : G) : (e (X0 ◇ X1)) = (v (w X0 ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)))) := by first | exact superpose eq430 eq4767 | exact mod_symm (superpose eq430 eq4767) | exact superpose eq4767 eq430 | exact mod_symm (superpose eq4767 eq430)
  have eq4983 (X0 X1 : G) : (e (X0 ◇ X1)) = (v (w X0 (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := by first | exact superpose eq649 eq4808 | exact mod_symm (superpose eq649 eq4808) | exact superpose eq4808 eq649 | exact mod_symm (superpose eq4808 eq649)
  have eq5080 (X0 X1 : G) : (e (X0 ◇ X1)) = (v ((w (X0 ◇ (X1 ◇ X1)) X0) ◇ (w X0 X1))) := by first | exact superpose eq1011 eq4983 | exact mod_symm (superpose eq1011 eq4983) | exact superpose eq4983 eq1011 | exact mod_symm (superpose eq4983 eq1011)
  have eq5138 (X0 X1 : G) : (e (X0 ◇ X1)) = (v ((w X0 X1) ◇ (w X0 (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq2349 eq5080 | exact mod_symm (superpose eq2349 eq5080) | exact superpose eq5080 eq2349 | exact mod_symm (superpose eq5080 eq2349)
  have eq5177 (X0 X1 : G) : (e (X0 ◇ X1)) = (v ((w X0 X1) ◇ ((w X1 X1) ◇ (w X0 X0)))) := by first | exact superpose eq1011 eq5138 | exact mod_symm (superpose eq1011 eq5138) | exact superpose eq5138 eq1011 | exact mod_symm (superpose eq5138 eq1011)
  have eq5203 (X0 X1 : G) : (w X0 X1) = (v ((w X0 X1) ◇ ((w X1 X1) ◇ (w X0 X0)))) := by first | exact superpose eq22 eq5177 | exact mod_symm (superpose eq22 eq5177) | exact superpose eq5177 eq22 | exact mod_symm (superpose eq5177 eq22)
  have eq5591 (X0 X1 : G) : (w (e X0) (e X1)) = (v (((e X0) ◇ ((e X0) ◇ ((e X1) ◇ (e X1)))) ◇ (w X1 X0))) := by first | exact superpose eq56 eq78 | exact mod_symm (superpose eq56 eq78) | exact superpose eq78 eq56 | exact mod_symm (superpose eq78 eq56)
  have eq5622 (X0 X1 : G) : (w (e X0) (e X1)) = (v (((e X0) ◇ ((e X1) ◇ (e X1))) ◇ (w (X0 ◇ X0) X1))) := by first | exact superpose eq994 eq5591 | exact mod_symm (superpose eq994 eq5591) | exact superpose eq5591 eq994 | exact mod_symm (superpose eq5591 eq994)
  have eq5677 (X0 X1 : G) : (w (e X0) (e X1)) = (v (((e X1) ◇ (e X1)) ◇ (w (X1 ◇ X0) (X0 ◇ X0)))) := by first | exact superpose eq994 eq5622 | exact mod_symm (superpose eq994 eq5622) | exact superpose eq5622 eq994 | exact mod_symm (superpose eq5622 eq994)
  have eq5727 (X0 X1 : G) : (w (e X0) (e X1)) = (v ((e X1) ◇ (w (X1 ◇ (X0 ◇ X0)) (X1 ◇ X0)))) := by first | exact superpose eq1119 eq5677 | exact mod_symm (superpose eq1119 eq5677) | exact superpose eq5677 eq1119 | exact mod_symm (superpose eq5677 eq1119)
  have eq5773 (X0 X1 : G) : (w (e X0) (e X1)) = (v (w X1 (w (X1 ◇ (X0 ◇ X0)) (X1 ◇ X0)))) := by first | exact superpose eq37 eq5727 | exact mod_symm (superpose eq37 eq5727) | exact superpose eq5727 eq37 | exact mod_symm (superpose eq5727 eq37)
  have eq5809 (X0 X1 : G) : (w (e X0) (e X1)) = (v (w X1 ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)))) := by first | exact superpose eq54 eq5773 | exact mod_symm (superpose eq54 eq5773) | exact superpose eq5773 eq54 | exact mod_symm (superpose eq5773 eq54)
  have eq5833 (X0 X1 : G) : (w (e X0) (e X1)) = (v (w X1 (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)))) := by first | exact superpose eq649 eq5809 | exact mod_symm (superpose eq649 eq5809) | exact superpose eq5809 eq649 | exact mod_symm (superpose eq5809 eq649)
  have eq5854 (X0 X1 : G) : (w (e X0) (e X1)) = (v ((w (X1 ◇ (X0 ◇ X0)) X1) ◇ (w X1 X0))) := by first | exact superpose eq1011 eq5833 | exact mod_symm (superpose eq1011 eq5833) | exact superpose eq5833 eq1011 | exact mod_symm (superpose eq5833 eq1011)
  have eq5868 (X0 X1 : G) : (w (e X0) (e X1)) = (v ((w X1 X0) ◇ (w X1 (X1 ◇ (X0 ◇ X0))))) := by first | exact superpose eq2349 eq5854 | exact mod_symm (superpose eq2349 eq5854) | exact superpose eq5854 eq2349 | exact mod_symm (superpose eq5854 eq2349)
  have eq5878 (X0 X1 : G) : (w (e X0) (e X1)) = (v ((w X1 X0) ◇ ((w X0 X0) ◇ (w X1 X1)))) := by first | exact superpose eq1011 eq5868 | exact mod_symm (superpose eq1011 eq5868) | exact superpose eq5868 eq1011 | exact mod_symm (superpose eq5868 eq1011)
  have eq5886 (X0 X1 : G) : (w (e X0) (e X1)) = (w X1 X0) := by first | exact superpose eq5203 eq5878 | exact mod_symm (superpose eq5203 eq5878) | exact superpose eq5878 eq5203 | exact mod_symm (superpose eq5878 eq5203)
  have eq5892 (X0 X1 : G) : (w X1 X0) = (w X0 (e X1)) := by first | exact superpose eq43 eq5886 | exact mod_symm (superpose eq43 eq5886) | exact superpose eq5886 eq43 | exact mod_symm (superpose eq5886 eq43)
  have eq5912 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq5892 eq42 | exact mod_symm (superpose eq5892 eq42) | exact superpose eq42 eq5892 | exact mod_symm (superpose eq42 eq5892)
  have eq6542 : (w x (w y z)) ≠ (w y (w z x)) := by first | exact superpose eq5912 eq23 | exact mod_symm (superpose eq5912 eq23) | exact superpose eq23 eq5912 | exact mod_symm (superpose eq23 eq5912)
  subsumption eq6542 eq2676


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
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ ((v a) ◇ (v a)))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ (a ◇ a))) = e a := fun a ↦ he.v_comp_u a
  rw [@Law332.models_iff]
  intro x y
  exact aux4364_332 h e v _ heh hvh he.idem he.comm_v hu huv hvu (fun a b ↦ rfl) x y

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
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ ((v a) ◇ (v a)))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ (a ◇ a))) = e a := fun a ↦ he.v_comp_u a
  rw [@Law4343.models_iff]
  intro x y
  exact aux4364_4343 h e v _ heh hvh he.idem he.comm_v hu huv hvu (fun a b ↦ rfl) x y

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
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a := fun a ↦ he.v_comp_u a
  rw [@Law4541.models_iff]
  intro x y z
  exact aux4364_4541 h e v _ heh hvh he.idem he.comm_v hu huv hvu (fun a b ↦ rfl) x y z

end Law.MagmaLaw
