import equational_theories.Definability.OuterIterate
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Source 4541: cells landed by an idempotent iterate applied outside the defining term

Equation 4541 `x ◇ (y ◇ z) = (z ◇ x) ◇ y` makes the unary term (x(xx)), (x(x(xx))) a magma endomorphism, so every iterate of it
distributes over `◇` and a defining term may be wrapped in one. `OuterIterate.lean` names the two
families of iterates the device can reach -- `v^[k] = u^[N k]` and `e ∘ v^[k] = u^[N k + N + 1]` --
and each cell below picks the wrapper and the base term that its target needs.

The endomorphism fact is proved from equation 4541 alone; the exponent is chosen after the magma,
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


/-- `u a = (a ◇ (a ◇ a))` is a magma endomorphism, from equation 4541 alone. -/
private theorem endo4541_0 [Magma G] (h : Equation4541 G) (x y : G) :
    ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) = (x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y)) := by
  by_contra nh
  have eq6 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq7 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ ((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) := mod_symm nh
  have eq8 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq9 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ ((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ x)) := by first | exact superpose eq6 eq7 | exact mod_symm (superpose eq6 eq7) | exact superpose eq7 eq6 | exact mod_symm (superpose eq7 eq6)
  have eq10 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ (x ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ x)) := by first | exact superpose eq6 eq9 | exact mod_symm (superpose eq6 eq9) | exact superpose eq9 eq6 | exact mod_symm (superpose eq9 eq6)
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by first | exact superpose eq6 eq8 | exact mod_symm (superpose eq6 eq8) | exact superpose eq8 eq6 | exact mod_symm (superpose eq8 eq6)
  have eq12 : ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ≠ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) := by first | exact superpose eq6 eq10 | exact mod_symm (superpose eq6 eq10) | exact superpose eq10 eq6 | exact mod_symm (superpose eq10 eq6)
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = (X2 ◇ ((X3 ◇ X0) ◇ X1)) := by first | exact superpose eq6 eq11 | exact mod_symm (superpose eq6 eq11) | exact superpose eq11 eq6 | exact mod_symm (superpose eq11 eq6)
  have eq14 : (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) ≠ (y ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ x)) := by first | exact superpose eq6 eq12 | exact mod_symm (superpose eq6 eq12) | exact superpose eq12 eq6 | exact mod_symm (superpose eq12 eq6)
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by first | exact superpose eq6 eq13 | exact mod_symm (superpose eq6 eq13) | exact superpose eq13 eq6 | exact mod_symm (superpose eq13 eq6)
  have eq16 : (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) ≠ (y ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))) := by first | exact superpose eq6 eq14 | exact mod_symm (superpose eq6 eq14) | exact superpose eq14 eq6 | exact mod_symm (superpose eq14 eq6)
  have eq17 : (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) ≠ (x ◇ ((x ◇ y) ◇ (y ◇ (x ◇ y)))) := by first | exact superpose eq15 eq16 | exact mod_symm (superpose eq15 eq16) | exact superpose eq16 eq15 | exact mod_symm (superpose eq16 eq15)
  have eq18 : (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) ≠ (x ◇ (y ◇ ((y ◇ (x ◇ y)) ◇ x))) := by first | exact superpose eq6 eq17 | exact mod_symm (superpose eq6 eq17) | exact superpose eq17 eq6 | exact mod_symm (superpose eq17 eq6)
  have eq19 : (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) ≠ (x ◇ (y ◇ ((x ◇ y) ◇ (x ◇ y)))) := by first | exact superpose eq6 eq18 | exact mod_symm (superpose eq6 eq18) | exact superpose eq18 eq6 | exact mod_symm (superpose eq18 eq6)
  have eq20 : (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) ≠ (x ◇ (x ◇ (y ◇ (y ◇ (x ◇ y))))) := by first | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19) | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15)
  have eq21 : (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) ≠ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  first | exact eq21 rfl | exact eq21 _ rfl | exact eq21 _ _ rfl | exact eq21 _ _ _ rfl


/-- `u a = (a ◇ (a ◇ (a ◇ a)))` is a magma endomorphism, from equation 4541 alone. -/
private theorem endo4541_1 [Magma G] (h : Equation4541 G) (x y : G) :
    ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) = (x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (y ◇ (y ◇ y))) := by
  by_contra nh
  have eq6 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq7 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (y ◇ (y ◇ y)))) := mod_symm nh
  have eq8 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by first | exact superpose eq6 eq8 | exact mod_symm (superpose eq6 eq8) | exact superpose eq8 eq6 | exact mod_symm (superpose eq8 eq6)
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = (X2 ◇ ((X3 ◇ X0) ◇ X1)) := by first | exact superpose eq6 eq11 | exact mod_symm (superpose eq6 eq11) | exact superpose eq11 eq6 | exact mod_symm (superpose eq11 eq6)
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by first | exact superpose eq6 eq13 | exact mod_symm (superpose eq6 eq13) | exact superpose eq13 eq6 | exact mod_symm (superpose eq13 eq6)
  have eq43 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X5))) = (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by first | exact superpose eq15 eq15 | exact mod_symm (superpose eq15 eq15) | exact superpose eq15 eq15 | exact mod_symm (superpose eq15 eq15)
  have eq44 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X4 ◇ (X3 ◇ X0)))) = (X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := by first | exact superpose eq6 eq15 | exact mod_symm (superpose eq6 eq15) | exact superpose eq15 eq6 | exact mod_symm (superpose eq15 eq6)
  have eq46 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X2))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by first | exact superpose eq15 eq15 | exact mod_symm (superpose eq15 eq15) | exact superpose eq15 eq15 | exact mod_symm (superpose eq15 eq15)
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X2)) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) := by first | exact superpose eq15 eq6 | exact mod_symm (superpose eq15 eq6) | exact superpose eq6 eq15 | exact mod_symm (superpose eq6 eq15)
  have eq56 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X2)) = ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) := by first | exact superpose eq6 eq51 | exact mod_symm (superpose eq6 eq51) | exact superpose eq51 eq6 | exact mod_symm (superpose eq51 eq6)
  have eq61 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X3 ◇ (X1 ◇ ((X4 ◇ X2) ◇ X0))) := by first | exact superpose eq6 eq46 | exact mod_symm (superpose eq6 eq46) | exact superpose eq46 eq6 | exact mod_symm (superpose eq46 eq6)
  have eq63 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X4 ◇ (X3 ◇ X0)))) = (X4 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) := by first | exact superpose eq6 eq44 | exact mod_symm (superpose eq6 eq44) | exact superpose eq44 eq6 | exact mod_symm (superpose eq44 eq6)
  have eq64 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X2 ◇ ((X0 ◇ X1) ◇ ((X4 ◇ X5) ◇ X3))) := by first | exact superpose eq6 eq43 | exact mod_symm (superpose eq6 eq43) | exact superpose eq43 eq6 | exact mod_symm (superpose eq43 eq6)
  have eq76 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X2)) = ((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ X1)) := by first | exact superpose eq6 eq56 | exact mod_symm (superpose eq6 eq56) | exact superpose eq56 eq6 | exact mod_symm (superpose eq56 eq6)
  have eq81 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X4)))) := by first | exact superpose eq6 eq61 | exact mod_symm (superpose eq6 eq61) | exact superpose eq61 eq6 | exact mod_symm (superpose eq61 eq6)
  have eq83 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X2 ◇ (X1 ◇ (((X4 ◇ X5) ◇ X3) ◇ X0))) := by first | exact superpose eq6 eq64 | exact mod_symm (superpose eq6 eq64) | exact superpose eq64 eq6 | exact mod_symm (superpose eq64 eq6)
  have eq94 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X2)) = (X3 ◇ (((X4 ◇ X0) ◇ X1) ◇ X2)) := by first | exact superpose eq6 eq76 | exact mod_symm (superpose eq6 eq76) | exact superpose eq76 eq6 | exact mod_symm (superpose eq76 eq6)
  have eq99 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X5))))) := by first | exact superpose eq6 eq83 | exact mod_symm (superpose eq6 eq83) | exact superpose eq83 eq6 | exact mod_symm (superpose eq83 eq6)
  have eq108 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X2)) = (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ X0)))) := by first | exact superpose eq6 eq94 | exact mod_symm (superpose eq6 eq94) | exact superpose eq94 eq6 | exact mod_symm (superpose eq94 eq6)
  have eq117 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ X0)))) = ((X0 ◇ X1) ◇ ((X4 ◇ X2) ◇ X3)) := by first | exact superpose eq6 eq108 | exact mod_symm (superpose eq6 eq108) | exact superpose eq108 eq6 | exact mod_symm (superpose eq108 eq6)
  have eq121 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ X0)))) = (X1 ◇ (((X4 ◇ X2) ◇ X3) ◇ X0)) := by first | exact superpose eq6 eq117 | exact mod_symm (superpose eq6 eq117) | exact superpose eq117 eq6 | exact mod_symm (superpose eq117 eq6)
  have eq125 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ X0)))) = (X1 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X2)))) := by first | exact superpose eq6 eq121 | exact mod_symm (superpose eq6 eq121) | exact superpose eq121 eq6 | exact mod_symm (superpose eq121 eq6)
  have eq181 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X3 ◇ (X4 ◇ ((X2 ◇ X0) ◇ X5)))) = (X4 ◇ (X5 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by first | exact superpose eq6 eq63 | exact mod_symm (superpose eq6 eq63) | exact superpose eq63 eq6 | exact mod_symm (superpose eq63 eq6)
  have eq193 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X1 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2)))) := by first | exact superpose eq15 eq63 | exact mod_symm (superpose eq15 eq63) | exact superpose eq63 eq15 | exact mod_symm (superpose eq63 eq15)
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = (X5 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4)) := by first | exact superpose eq63 eq6 | exact mod_symm (superpose eq63 eq6) | exact superpose eq6 eq63 | exact mod_symm (superpose eq6 eq63)
  have eq212 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X4 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ (X5 ◇ X2))) := by first | exact superpose eq63 eq15 | exact mod_symm (superpose eq63 eq15) | exact superpose eq15 eq63 | exact mod_symm (superpose eq15 eq63)
  have eq217 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5)))) = (X3 ◇ ((X5 ◇ (X1 ◇ (X4 ◇ X0))) ◇ X2)) := by first | exact superpose eq63 eq6 | exact mod_symm (superpose eq63 eq6) | exact superpose eq6 eq63 | exact mod_symm (superpose eq6 eq63)
  have eq218 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5)))) = (X3 ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (X2 ◇ X5))) := by first | exact superpose eq6 eq217 | exact mod_symm (superpose eq6 eq217) | exact superpose eq217 eq6 | exact mod_symm (superpose eq217 eq6)
  have eq223 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X4 ◇ ((X3 ◇ X0) ◇ ((X5 ◇ X2) ◇ X1))) := by first | exact superpose eq6 eq212 | exact mod_symm (superpose eq6 eq212) | exact superpose eq212 eq6 | exact mod_symm (superpose eq212 eq6)
  have eq227 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = (X5 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X2))) := by first | exact superpose eq6 eq208 | exact mod_symm (superpose eq6 eq208) | exact superpose eq208 eq6 | exact mod_symm (superpose eq208 eq6)
  have eq251 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = (X1 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X5 ◇ X2))))) := by first | exact superpose eq6 eq181 | exact mod_symm (superpose eq6 eq181) | exact superpose eq181 eq6 | exact mod_symm (superpose eq181 eq6)
  have eq268 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5)))) = (X3 ◇ ((X4 ◇ X0) ◇ ((X2 ◇ X5) ◇ X1))) := by first | exact superpose eq6 eq218 | exact mod_symm (superpose eq6 eq218) | exact superpose eq218 eq6 | exact mod_symm (superpose eq218 eq6)
  have eq273 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X4 ◇ (X0 ◇ (((X5 ◇ X2) ◇ X1) ◇ X3))) := by first | exact superpose eq6 eq223 | exact mod_symm (superpose eq6 eq223) | exact superpose eq223 eq6 | exact mod_symm (superpose eq223 eq6)
  have eq277 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = (X5 ◇ ((X3 ◇ X1) ◇ ((X4 ◇ X2) ◇ X0))) := by first | exact superpose eq6 eq227 | exact mod_symm (superpose eq6 eq227) | exact superpose eq227 eq6 | exact mod_symm (superpose eq227 eq6)
  have eq312 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5)))) = (X3 ◇ (X0 ◇ (((X2 ◇ X5) ◇ X1) ◇ X4))) := by first | exact superpose eq6 eq268 | exact mod_symm (superpose eq6 eq268) | exact superpose eq268 eq6 | exact mod_symm (superpose eq268 eq6)
  have eq317 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X4 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X5 ◇ X2))))) := by first | exact superpose eq6 eq273 | exact mod_symm (superpose eq6 eq273) | exact superpose eq273 eq6 | exact mod_symm (superpose eq273 eq6)
  have eq319 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = (X5 ◇ (X1 ◇ (((X4 ◇ X2) ◇ X0) ◇ X3))) := by first | exact superpose eq6 eq277 | exact mod_symm (superpose eq6 eq277) | exact superpose eq277 eq6 | exact mod_symm (superpose eq277 eq6)
  have eq352 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5)))) = (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ (X2 ◇ X5))))) := by first | exact superpose eq6 eq312 | exact mod_symm (superpose eq6 eq312) | exact superpose eq312 eq6 | exact mod_symm (superpose eq312 eq6)
  have eq357 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = (X5 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X2))))) := by first | exact superpose eq6 eq319 | exact mod_symm (superpose eq6 eq319) | exact superpose eq319 eq6 | exact mod_symm (superpose eq319 eq6)
  have eq379 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ (X2 ◇ X5))))) = (X0 ◇ (X1 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X2)))) := by first | exact superpose eq6 eq352 | exact mod_symm (superpose eq6 eq352) | exact superpose eq352 eq6 | exact mod_symm (superpose eq352 eq6)
  have eq400 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ (X2 ◇ X5))))) = (X0 ◇ (X1 ◇ (X3 ◇ (X5 ◇ (X2 ◇ X4))))) := by first | exact superpose eq6 eq379 | exact mod_symm (superpose eq6 eq379) | exact superpose eq379 eq6 | exact mod_symm (superpose eq379 eq6)
  have eq473 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ (X6 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = ((X0 ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X2 ◇ (X6 ◇ X5)))) := by first | exact superpose eq63 eq81 | exact mod_symm (superpose eq63 eq81) | exact superpose eq81 eq63 | exact mod_symm (superpose eq81 eq63)
  have eq478 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X5)))) := by first | exact superpose eq81 eq81 | exact mod_symm (superpose eq81 eq81) | exact superpose eq81 eq81 | exact mod_symm (superpose eq81 eq81)
  have eq509 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) := by first | exact superpose eq81 eq81 | exact mod_symm (superpose eq81 eq81) | exact superpose eq81 eq81 | exact mod_symm (superpose eq81 eq81)
  have eq514 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = (X0 ◇ (X1 ◇ (X4 ◇ (X2 ◇ X3)))) := by first | exact superpose eq81 eq63 | exact mod_symm (superpose eq81 eq63) | exact superpose eq63 eq81 | exact mod_symm (superpose eq63 eq81)
  have eq515 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = (X1 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X4)))) := by first | exact superpose eq81 eq63 | exact mod_symm (superpose eq81 eq63) | exact superpose eq63 eq81 | exact mod_symm (superpose eq63 eq81)
  have eq531 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X2)))) := by first | exact superpose eq81 eq63 | exact mod_symm (superpose eq81 eq63) | exact superpose eq63 eq81 | exact mod_symm (superpose eq63 eq81)
  have eq546 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (y ◇ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x))))))) := by first | exact superpose eq81 eq7 | exact mod_symm (superpose eq81 eq7) | exact superpose eq7 eq81 | exact mod_symm (superpose eq7 eq81)
  have eq549 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (y ◇ ((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))))) := by first | exact superpose eq99 eq546 | exact mod_symm (superpose eq99 eq546) | exact superpose eq546 eq99 | exact mod_symm (superpose eq546 eq99)
  have eq605 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X0 ◇ ((X3 ◇ (X1 ◇ (X4 ◇ X5))) ◇ X2)) := by first | exact superpose eq6 eq478 | exact mod_symm (superpose eq6 eq478) | exact superpose eq478 eq6 | exact mod_symm (superpose eq478 eq6)
  have eq608 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ (X6 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = ((X3 ◇ X1) ◇ ((X4 ◇ (X2 ◇ (X6 ◇ X5))) ◇ X0)) := by first | exact superpose eq6 eq473 | exact mod_symm (superpose eq6 eq473) | exact superpose eq473 eq6 | exact mod_symm (superpose eq473 eq6)
  have eq623 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (x ◇ (x ◇ x)))))) := by first | exact superpose eq531 eq549 | exact mod_symm (superpose eq531 eq549) | exact superpose eq549 eq531 | exact mod_symm (superpose eq549 eq531)
  have eq679 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X0 ◇ ((X1 ◇ (X4 ◇ X5)) ◇ (X2 ◇ X3))) := by first | exact superpose eq6 eq605 | exact mod_symm (superpose eq6 eq605) | exact superpose eq605 eq6 | exact mod_symm (superpose eq605 eq6)
  have eq682 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ (X6 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = (X1 ◇ (((X4 ◇ (X2 ◇ (X6 ◇ X5))) ◇ X0) ◇ X3)) := by first | exact superpose eq6 eq608 | exact mod_symm (superpose eq6 eq608) | exact superpose eq608 eq6 | exact mod_symm (superpose eq608 eq6)
  have eq697 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (y ◇ (y ◇ ((x ◇ (x ◇ x)) ◇ (y ◇ y))))) := by first | exact superpose eq514 eq623 | exact mod_symm (superpose eq514 eq623) | exact superpose eq623 eq514 | exact mod_symm (superpose eq623 eq514)
  have eq744 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X0 ◇ ((X4 ◇ X5) ◇ ((X2 ◇ X3) ◇ X1))) := by first | exact superpose eq6 eq679 | exact mod_symm (superpose eq6 eq679) | exact superpose eq679 eq6 | exact mod_symm (superpose eq679 eq6)
  have eq747 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ (X6 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = (X1 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X2 ◇ (X6 ◇ X5)))))) := by first | exact superpose eq6 eq682 | exact mod_symm (superpose eq6 eq682) | exact superpose eq682 eq6 | exact mod_symm (superpose eq682 eq6)
  have eq761 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (y ◇ (y ◇ (y ◇ ((x ◇ (x ◇ x)) ◇ y))))) := by first | exact superpose eq81 eq697 | exact mod_symm (superpose eq81 eq697) | exact superpose eq697 eq81 | exact mod_symm (superpose eq697 eq81)
  have eq794 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X0 ◇ (X5 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4))) := by first | exact superpose eq6 eq744 | exact mod_symm (superpose eq6 eq744) | exact superpose eq744 eq6 | exact mod_symm (superpose eq744 eq6)
  have eq804 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ x))))))) := by first | exact superpose eq193 eq761 | exact mod_symm (superpose eq193 eq761) | exact superpose eq761 eq193 | exact mod_symm (superpose eq761 eq193)
  have eq831 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X0 ◇ (X5 ◇ (X1 ◇ (X4 ◇ (X2 ◇ X3))))) := by first | exact superpose eq6 eq794 | exact mod_symm (superpose eq6 eq794) | exact superpose eq794 eq6 | exact mod_symm (superpose eq794 eq6)
  have eq840 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ (y ◇ (y ◇ y)))))) := by first | exact superpose eq99 eq804 | exact mod_symm (superpose eq99 eq804) | exact superpose eq804 eq99 | exact mod_symm (superpose eq804 eq99)
  have eq856 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (y ◇ (y ◇ ((y ◇ y) ◇ (x ◇ x)))))) := by first | exact superpose eq831 eq840 | exact mod_symm (superpose eq831 eq840) | exact superpose eq840 eq831 | exact mod_symm (superpose eq840 eq831)
  have eq872 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ ((y ◇ y) ◇ (y ◇ y)))))) := by first | exact superpose eq747 eq856 | exact mod_symm (superpose eq747 eq856) | exact superpose eq856 eq747 | exact mod_symm (superpose eq856 eq747)
  have eq886 : ((x ◇ y) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq400 eq872 | exact mod_symm (superpose eq400 eq872) | exact superpose eq872 eq400 | exact mod_symm (superpose eq872 eq400)
  have eq890 : (y ◇ (((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ x)) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq6 eq886 | exact mod_symm (superpose eq6 eq886) | exact superpose eq886 eq6 | exact mod_symm (superpose eq886 eq6)
  have eq894 : (y ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (x ◇ y)))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq6 eq890 | exact mod_symm (superpose eq6 eq890) | exact superpose eq890 eq6 | exact mod_symm (superpose eq890 eq6)
  have eq898 : (x ◇ ((x ◇ y) ◇ (y ◇ ((x ◇ y) ◇ (x ◇ y))))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq15 eq894 | exact mod_symm (superpose eq15 eq894) | exact superpose eq894 eq15 | exact mod_symm (superpose eq894 eq15)
  have eq900 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (y ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))))) := by first | exact superpose eq509 eq898 | exact mod_symm (superpose eq509 eq898) | exact superpose eq898 eq509 | exact mod_symm (superpose eq898 eq509)
  have eq902 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (y ◇ ((x ◇ y) ◇ (y ◇ (x ◇ (x ◇ y)))))) := by first | exact superpose eq99 eq900 | exact mod_symm (superpose eq99 eq900) | exact superpose eq900 eq99 | exact mod_symm (superpose eq900 eq99)
  have eq904 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (y ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ (x ◇ y))))) := by first | exact superpose eq514 eq902 | exact mod_symm (superpose eq514 eq902) | exact superpose eq902 eq514 | exact mod_symm (superpose eq902 eq514)
  have eq906 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (y ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ (y ◇ y))))) := by first | exact superpose eq251 eq904 | exact mod_symm (superpose eq251 eq904) | exact superpose eq904 eq251 | exact mod_symm (superpose eq904 eq251)
  have eq908 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ (y ◇ (y ◇ y))))) := by first | exact superpose eq509 eq906 | exact mod_symm (superpose eq509 eq906) | exact superpose eq906 eq509 | exact mod_symm (superpose eq906 eq509)
  have eq910 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ ((y ◇ y) ◇ (y ◇ (x ◇ (x ◇ y)))))) := by first | exact superpose eq125 eq908 | exact mod_symm (superpose eq125 eq908) | exact superpose eq908 eq125 | exact mod_symm (superpose eq908 eq125)
  have eq912 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (x ◇ y)))))) := by first | exact superpose eq515 eq910 | exact mod_symm (superpose eq515 eq910) | exact superpose eq910 eq515 | exact mod_symm (superpose eq910 eq515)
  have eq914 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ (y ◇ ((x ◇ y) ◇ ((y ◇ y) ◇ x))))) := by first | exact superpose eq317 eq912 | exact mod_symm (superpose eq317 eq912) | exact superpose eq912 eq317 | exact mod_symm (superpose eq912 eq317)
  have eq916 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ (x ◇ ((x ◇ y) ◇ ((y ◇ y) ◇ y))))) := by first | exact superpose eq357 eq914 | exact mod_symm (superpose eq357 eq914) | exact superpose eq914 eq357 | exact mod_symm (superpose eq914 eq357)
  have eq918 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ (x ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y)))))) := by first | exact superpose eq400 eq916 | exact mod_symm (superpose eq400 eq916) | exact superpose eq916 eq400 | exact mod_symm (superpose eq916 eq400)
  have eq920 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ ((y ◇ y) ◇ x)))))) := by first | exact superpose eq317 eq918 | exact mod_symm (superpose eq317 eq918) | exact superpose eq918 eq317 | exact mod_symm (superpose eq918 eq317)
  have eq922 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y)))))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq357 eq920 | exact mod_symm (superpose eq357 eq920) | exact superpose eq920 eq357 | exact mod_symm (superpose eq920 eq357)
  have eq924 : (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))) := by first | exact superpose eq831 eq922 | exact mod_symm (superpose eq831 eq922) | exact superpose eq922 eq831 | exact mod_symm (superpose eq922 eq831)
  first | exact eq924 rfl | exact eq924 _ rfl | exact eq924 _ _ rfl | exact eq924 _ _ _ rfl


/-- Equation 332 `x ◇ y = y ◇ (x ◇ x)` is term-definable from equation 4541 over finite magmas, via the term
`x □ y := (((x ◇ x) ◇ y) ◇ y)` with `u a = (a ◇ (a ◇ (a ◇ a)))`
taken at u^[2N+1]. -/
private theorem aux4541_332 [Magma G] (h : Equation4541 G) (e v : G → G) (w : G → G → G)
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
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq16 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq18 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq19 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq21 (X0 : G) : (e X0) = (v (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := mod_symm (hvu ..)
  have eq22 (X0 X1 : G) : (w X0 X1) = (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) := mod_symm (hw ..)
  have eq23 : (w x y) ≠ (w y (w x x)) := mod_symm nh
  have eq27 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq18 eq16 | exact mod_symm (superpose eq18 eq16) | exact superpose eq16 eq18 | exact mod_symm (superpose eq16 eq18)
  have eq28 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq18 eq16 | exact mod_symm (superpose eq18 eq16) | exact superpose eq16 eq18 | exact mod_symm (superpose eq16 eq18)
  have eq29 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq16 eq28 | exact mod_symm (superpose eq16 eq28) | exact superpose eq28 eq16 | exact mod_symm (superpose eq28 eq16)
  have eq30 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq27 | exact mod_symm (superpose eq16 eq27) | exact superpose eq27 eq16 | exact mod_symm (superpose eq27 eq16)
  have eq33 (X0 X1 X2 : G) : ((e X1) ◇ (X2 ◇ (e X0))) = ((e (X0 ◇ X1)) ◇ X2) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq44 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq29 eq19 | exact mod_symm (superpose eq29 eq19) | exact superpose eq19 eq29 | exact mod_symm (superpose eq19 eq29)
  have eq46 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq19 eq44 | exact mod_symm (superpose eq19 eq44) | exact superpose eq44 eq19 | exact mod_symm (superpose eq44 eq19)
  have eq54 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((e X0) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq16 eq21 | exact mod_symm (superpose eq16 eq21) | exact superpose eq21 eq16 | exact mod_symm (superpose eq21 eq16)
  have eq66 (X0 : G) : (e (e X0)) = (v ((e ((X0 ◇ X0) ◇ X0)) ◇ (e X0))) := by first | exact superpose eq33 eq54 | exact mod_symm (superpose eq33 eq54) | exact superpose eq54 eq33 | exact mod_symm (superpose eq54 eq33)
  have eq72 (X0 : G) : (e (e X0)) = (v (e (((X0 ◇ X0) ◇ X0) ◇ X0))) := by first | exact superpose eq16 eq66 | exact mod_symm (superpose eq16 eq66) | exact superpose eq66 eq16 | exact mod_symm (superpose eq66 eq16)
  have eq78 (X0 : G) : (e (e X0)) = (e (v (((X0 ◇ X0) ◇ X0) ◇ X0))) := by first | exact superpose eq19 eq72 | exact mod_symm (superpose eq19 eq72) | exact superpose eq72 eq19 | exact mod_symm (superpose eq72 eq19)
  have eq84 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq22 eq78 | exact mod_symm (superpose eq22 eq78) | exact superpose eq78 eq22 | exact mod_symm (superpose eq78 eq22)
  have eq88 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq18 eq84 | exact mod_symm (superpose eq18 eq84) | exact superpose eq84 eq18 | exact mod_symm (superpose eq84 eq18)
  have eq100 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq88 eq23 | exact mod_symm (superpose eq88 eq23) | exact superpose eq23 eq88 | exact mod_symm (superpose eq23 eq88)
  have eq104 (X0 X1 : G) : (w X0 X1) = (e (v ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := by first | exact superpose eq14 eq22 | exact mod_symm (superpose eq14 eq22) | exact superpose eq22 eq14 | exact mod_symm (superpose eq22 eq14)
  have eq105 (X0 X1 : G) : (w X1 X0) = (e (v (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq14 eq22 | exact mod_symm (superpose eq14 eq22) | exact superpose eq22 eq14 | exact mod_symm (superpose eq22 eq14)
  have eq115 (X0 X1 : G) : (w X0 X1) = (e (v ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by first | exact superpose eq14 eq104 | exact mod_symm (superpose eq14 eq104) | exact superpose eq104 eq14 | exact mod_symm (superpose eq104 eq14)
  have eq120 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := by first | exact superpose eq14 eq115 | exact mod_symm (superpose eq14 eq115) | exact superpose eq115 eq14 | exact mod_symm (superpose eq115 eq14)
  have eq122 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq14 eq120 | exact mod_symm (superpose eq14 eq120) | exact superpose eq120 eq14 | exact mod_symm (superpose eq120 eq14)
  have eq1136 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq30 eq19 | exact mod_symm (superpose eq30 eq19) | exact superpose eq19 eq30 | exact mod_symm (superpose eq19 eq30)
  have eq1138 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq19 eq1136 | exact mod_symm (superpose eq19 eq1136) | exact superpose eq1136 eq19 | exact mod_symm (superpose eq1136 eq19)
  have eq1263 (X0 X1 : G) : (w X0 (e X1)) = (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq46 eq22 | exact mod_symm (superpose eq46 eq22) | exact superpose eq22 eq46 | exact mod_symm (superpose eq22 eq46)
  have eq1279 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((e X1) ◇ (X1 ◇ (X0 ◇ X0))))) := by first | exact superpose eq14 eq1263 | exact mod_symm (superpose eq14 eq1263) | exact superpose eq1263 eq14 | exact mod_symm (superpose eq1263 eq14)
  have eq1288 (X0 X1 : G) : (w X0 (e X1)) = (e (v (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by first | exact superpose eq1138 eq1279 | exact mod_symm (superpose eq1138 eq1279) | exact superpose eq1279 eq1138 | exact mod_symm (superpose eq1279 eq1138)
  have eq1291 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq105 eq1288 | exact mod_symm (superpose eq105 eq1288) | exact superpose eq1288 eq105 | exact mod_symm (superpose eq1288 eq105)
  have eq1339 : (w x y) ≠ (w y x) := by first | exact superpose eq1291 eq100 | exact mod_symm (superpose eq1291 eq100) | exact superpose eq100 eq1291 | exact mod_symm (superpose eq100 eq1291)
  have eq1359 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq122 eq105 | exact mod_symm (superpose eq122 eq105) | exact superpose eq105 eq122 | exact mod_symm (superpose eq105 eq122)
  have eq1591 : (w x y) ≠ (w x y) := by first | exact superpose eq1359 eq1339 | exact mod_symm (superpose eq1359 eq1339) | exact superpose eq1339 eq1359 | exact mod_symm (superpose eq1339 eq1359)
  first | exact eq1591 rfl | exact eq1591 _ rfl | exact eq1591 _ _ rfl | exact eq1591 _ _ _ rfl


/-- Equation 4343 `x ◇ (y ◇ y) = y ◇ (x ◇ x)` is term-definable from equation 4541 over finite magmas, via the term
`x □ y := (((x ◇ x) ◇ y) ◇ y)` with `u a = (a ◇ (a ◇ (a ◇ a)))`
taken at u^[2N+1]. -/
private theorem aux4541_4343 [Magma G] (h : Equation4541 G) (e v : G → G) (w : G → G → G)
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
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq16 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq18 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq19 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq21 (X0 : G) : (e X0) = (v (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := mod_symm (hvu ..)
  have eq22 (X0 X1 : G) : (w X0 X1) = (e (v (((X0 ◇ X0) ◇ X1) ◇ X1))) := mod_symm (hw ..)
  have eq23 : (w x (w y y)) ≠ (w y (w x x)) := mod_symm nh
  have eq27 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq18 eq16 | exact mod_symm (superpose eq18 eq16) | exact superpose eq16 eq18 | exact mod_symm (superpose eq16 eq18)
  have eq28 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq18 eq16 | exact mod_symm (superpose eq18 eq16) | exact superpose eq16 eq18 | exact mod_symm (superpose eq16 eq18)
  have eq29 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq16 eq28 | exact mod_symm (superpose eq16 eq28) | exact superpose eq28 eq16 | exact mod_symm (superpose eq28 eq16)
  have eq30 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq27 | exact mod_symm (superpose eq16 eq27) | exact superpose eq27 eq16 | exact mod_symm (superpose eq27 eq16)
  have eq33 (X0 X1 X2 : G) : ((e X1) ◇ (X2 ◇ (e X0))) = ((e (X0 ◇ X1)) ◇ X2) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq44 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq29 eq19 | exact mod_symm (superpose eq29 eq19) | exact superpose eq19 eq29 | exact mod_symm (superpose eq19 eq29)
  have eq46 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq19 eq44 | exact mod_symm (superpose eq19 eq44) | exact superpose eq44 eq19 | exact mod_symm (superpose eq44 eq19)
  have eq54 (X0 : G) : (e (e X0)) = (v ((e X0) ◇ ((e X0) ◇ (e (X0 ◇ X0))))) := by first | exact superpose eq16 eq21 | exact mod_symm (superpose eq16 eq21) | exact superpose eq21 eq16 | exact mod_symm (superpose eq21 eq16)
  have eq66 (X0 : G) : (e (e X0)) = (v ((e ((X0 ◇ X0) ◇ X0)) ◇ (e X0))) := by first | exact superpose eq33 eq54 | exact mod_symm (superpose eq33 eq54) | exact superpose eq54 eq33 | exact mod_symm (superpose eq54 eq33)
  have eq72 (X0 : G) : (e (e X0)) = (v (e (((X0 ◇ X0) ◇ X0) ◇ X0))) := by first | exact superpose eq16 eq66 | exact mod_symm (superpose eq16 eq66) | exact superpose eq66 eq16 | exact mod_symm (superpose eq66 eq16)
  have eq78 (X0 : G) : (e (e X0)) = (e (v (((X0 ◇ X0) ◇ X0) ◇ X0))) := by first | exact superpose eq19 eq72 | exact mod_symm (superpose eq19 eq72) | exact superpose eq72 eq19 | exact mod_symm (superpose eq72 eq19)
  have eq84 (X0 : G) : (e (e X0)) = (w X0 X0) := by first | exact superpose eq22 eq78 | exact mod_symm (superpose eq22 eq78) | exact superpose eq78 eq22 | exact mod_symm (superpose eq78 eq22)
  have eq88 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq18 eq84 | exact mod_symm (superpose eq18 eq84) | exact superpose eq84 eq18 | exact mod_symm (superpose eq84 eq18)
  have eq100 : (w x (w y y)) ≠ (w y (e x)) := by first | exact superpose eq88 eq23 | exact mod_symm (superpose eq88 eq23) | exact superpose eq23 eq88 | exact mod_symm (superpose eq23 eq88)
  have eq101 : (w y (e x)) ≠ (w x (e y)) := by first | exact superpose eq88 eq100 | exact mod_symm (superpose eq88 eq100) | exact superpose eq100 eq88 | exact mod_symm (superpose eq100 eq88)
  have eq105 (X0 X1 : G) : (w X0 X1) = (e (v ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := by first | exact superpose eq14 eq22 | exact mod_symm (superpose eq14 eq22) | exact superpose eq22 eq14 | exact mod_symm (superpose eq22 eq14)
  have eq106 (X0 X1 : G) : (w X1 X0) = (e (v (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq14 eq22 | exact mod_symm (superpose eq14 eq22) | exact superpose eq22 eq14 | exact mod_symm (superpose eq22 eq14)
  have eq116 (X0 X1 : G) : (w X0 X1) = (e (v ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by first | exact superpose eq14 eq105 | exact mod_symm (superpose eq14 eq105) | exact superpose eq105 eq14 | exact mod_symm (superpose eq105 eq14)
  have eq121 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := by first | exact superpose eq14 eq116 | exact mod_symm (superpose eq14 eq116) | exact superpose eq116 eq14 | exact mod_symm (superpose eq116 eq14)
  have eq123 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq14 eq121 | exact mod_symm (superpose eq14 eq121) | exact superpose eq121 eq14 | exact mod_symm (superpose eq121 eq14)
  have eq1137 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq30 eq19 | exact mod_symm (superpose eq30 eq19) | exact superpose eq19 eq30 | exact mod_symm (superpose eq19 eq30)
  have eq1139 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq19 eq1137 | exact mod_symm (superpose eq19 eq1137) | exact superpose eq1137 eq19 | exact mod_symm (superpose eq1137 eq19)
  have eq1264 (X0 X1 : G) : (w X0 (e X1)) = (e (v (((X0 ◇ X0) ◇ (e X1)) ◇ X1))) := by first | exact superpose eq46 eq22 | exact mod_symm (superpose eq46 eq22) | exact superpose eq22 eq46 | exact mod_symm (superpose eq22 eq46)
  have eq1280 (X0 X1 : G) : (w X0 (e X1)) = (e (v ((e X1) ◇ (X1 ◇ (X0 ◇ X0))))) := by first | exact superpose eq14 eq1264 | exact mod_symm (superpose eq14 eq1264) | exact superpose eq1264 eq14 | exact mod_symm (superpose eq1264 eq14)
  have eq1289 (X0 X1 : G) : (w X0 (e X1)) = (e (v (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by first | exact superpose eq1139 eq1280 | exact mod_symm (superpose eq1139 eq1280) | exact superpose eq1280 eq1139 | exact mod_symm (superpose eq1280 eq1139)
  have eq1292 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq106 eq1289 | exact mod_symm (superpose eq106 eq1289) | exact superpose eq1289 eq106 | exact mod_symm (superpose eq1289 eq106)
  have eq1340 : (w x (e y)) ≠ (w y x) := by first | exact superpose eq1292 eq101 | exact mod_symm (superpose eq1292 eq101) | exact superpose eq101 eq1292 | exact mod_symm (superpose eq101 eq1292)
  have eq1345 : (w y x) ≠ (w x y) := by first | exact superpose eq1292 eq1340 | exact mod_symm (superpose eq1292 eq1340) | exact superpose eq1340 eq1292 | exact mod_symm (superpose eq1340 eq1292)
  have eq1361 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq123 eq106 | exact mod_symm (superpose eq123 eq106) | exact superpose eq106 eq123 | exact mod_symm (superpose eq106 eq123)
  have eq1593 : (w x y) ≠ (w x y) := by first | exact superpose eq1361 eq1345 | exact mod_symm (superpose eq1361 eq1345) | exact superpose eq1345 eq1361 | exact mod_symm (superpose eq1345 eq1361)
  first | exact eq1593 rfl | exact eq1593 _ rfl | exact eq1593 _ _ rfl | exact eq1593 _ _ _ rfl


/-- Equation 4364 `x ◇ (y ◇ z) = y ◇ (z ◇ x)` is term-definable from equation 4541 over finite magmas, via the term
`x □ y := (x ◇ y)` with `u a = (a ◇ (a ◇ a))`
taken at u^[1N+1]. -/
private theorem aux4541_4364 [Magma G] (h : Equation4541 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huh : ∀ a b : G, ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ b))) = (a ◇ (a ◇ a)) ◇ (b ◇ (b ◇ b)))
    (huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a)
    (hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a)
    (hw : ∀ a b : G, w a b = (e ((a ◇ b))))
    (x y z : G) :
    (w x (w y z)) =
      (w y (w z x)) := by
  by_contra nh
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq16 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq17 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq18 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq21 (X0 : G) : (e X0) = (v (X0 ◇ (X0 ◇ X0))) := mod_symm (hvu ..)
  have eq22 (X0 X1 : G) : (e (X0 ◇ X1)) = (w X0 X1) := mod_symm (hw ..)
  have eq23 : (w x (w y z)) ≠ (w y (w z x)) := mod_symm nh
  have eq24 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (w X0 X1) := by first | exact superpose eq22 eq16 | exact mod_symm (superpose eq22 eq16) | exact superpose eq16 eq22 | exact mod_symm (superpose eq16 eq22)
  have eq35 (X0 X1 : G) : (w X1 (e X0)) = ((e X1) ◇ (e X0)) := by first | exact superpose eq18 eq24 | exact mod_symm (superpose eq18 eq24) | exact superpose eq24 eq18 | exact mod_symm (superpose eq24 eq18)
  have eq42 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq24 eq35 | exact mod_symm (superpose eq24 eq35) | exact superpose eq35 eq24 | exact mod_symm (superpose eq35 eq24)
  have eq46 (X0 X1 : G) : (v ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq21 eq17 | exact mod_symm (superpose eq21 eq17) | exact superpose eq17 eq21 | exact mod_symm (superpose eq17 eq21)
  have eq53 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by first | exact superpose eq14 eq46 | exact mod_symm (superpose eq14 eq46) | exact superpose eq46 eq14 | exact mod_symm (superpose eq46 eq14)
  have eq55 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by first | exact superpose eq14 eq53 | exact mod_symm (superpose eq14 eq53) | exact superpose eq53 eq14 | exact mod_symm (superpose eq53 eq14)
  have eq56 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by first | exact superpose eq14 eq55 | exact mod_symm (superpose eq14 eq55) | exact superpose eq55 eq14 | exact mod_symm (superpose eq55 eq14)
  have eq57 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq22 eq42 | exact mod_symm (superpose eq22 eq42) | exact superpose eq42 eq22 | exact mod_symm (superpose eq42 eq22)
  have eq62 (X0 X1 X2 : G) : (w (X2 ◇ X0) X1) = (e (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq14 eq22 | exact mod_symm (superpose eq14 eq22) | exact superpose eq22 eq14 | exact mod_symm (superpose eq22 eq14)
  have eq64 (X0 X1 : G) : (e (X1 ◇ X0)) = (v (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1))) := by first | exact superpose eq14 eq21 | exact mod_symm (superpose eq14 eq21) | exact superpose eq21 eq14 | exact mod_symm (superpose eq21 eq14)
  have eq65 (X0 X1 : G) : (e (X1 ◇ X0)) = (v (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq14 eq64 | exact mod_symm (superpose eq14 eq64) | exact superpose eq64 eq14 | exact mod_symm (superpose eq64 eq14)
  have eq67 (X0 X1 X2 : G) : (w X0 (X1 ◇ X2)) = (w (X2 ◇ X0) X1) := by first | exact superpose eq22 eq62 | exact mod_symm (superpose eq22 eq62) | exact superpose eq62 eq22 | exact mod_symm (superpose eq62 eq22)
  have eq69 (X0 X1 : G) : (e (X1 ◇ X0)) = (v (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) := by first | exact superpose eq14 eq65 | exact mod_symm (superpose eq14 eq65) | exact superpose eq65 eq14 | exact mod_symm (superpose eq65 eq14)
  have eq72 (X0 X1 : G) : (e (X1 ◇ X0)) = (v (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))))) := by first | exact superpose eq14 eq69 | exact mod_symm (superpose eq14 eq69) | exact superpose eq69 eq14 | exact mod_symm (superpose eq69 eq14)
  have eq75 (X0 X1 : G) : (e (X1 ◇ X0)) = (v (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))))) := by first | exact superpose eq14 eq72 | exact mod_symm (superpose eq14 eq72) | exact superpose eq72 eq14 | exact mod_symm (superpose eq72 eq14)
  have eq77 (X0 X1 : G) : (e (X1 ◇ X0)) = ((e X0) ◇ (v ((X1 ◇ X1) ◇ X1))) := by first | exact superpose eq56 eq75 | exact mod_symm (superpose eq56 eq75) | exact superpose eq75 eq56 | exact mod_symm (superpose eq75 eq56)
  have eq79 (X0 X1 : G) : (e (X1 ◇ X0)) = ((e X0) ◇ (v (X1 ◇ (X1 ◇ X1)))) := by first | exact superpose eq14 eq77 | exact mod_symm (superpose eq14 eq77) | exact superpose eq77 eq14 | exact mod_symm (superpose eq77 eq14)
  have eq81 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e (X1 ◇ X0)) := by first | exact superpose eq21 eq79 | exact mod_symm (superpose eq21 eq79) | exact superpose eq79 eq21 | exact mod_symm (superpose eq79 eq21)
  have eq82 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (w X1 X0) := by first | exact superpose eq22 eq81 | exact mod_symm (superpose eq22 eq81) | exact superpose eq81 eq22 | exact mod_symm (superpose eq81 eq22)
  have eq652 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq82 eq24 | exact mod_symm (superpose eq82 eq24) | exact superpose eq24 eq82 | exact mod_symm (superpose eq24 eq82)
  have eq914 (X0 X1 X2 : G) : (w X0 (X1 ◇ X2)) = (w X1 (X2 ◇ X0)) := by first | exact superpose eq67 eq652 | exact mod_symm (superpose eq67 eq652) | exact superpose eq652 eq67 | exact mod_symm (superpose eq652 eq67)
  have eq2232 : (w x (w y z)) ≠ (w y (z ◇ x)) := by first | exact superpose eq57 eq23 | exact mod_symm (superpose eq57 eq23) | exact superpose eq23 eq57 | exact mod_symm (superpose eq23 eq57)
  have eq2233 : (w x (w y z)) ≠ (w x (y ◇ z)) := by first | exact superpose eq914 eq2232 | exact mod_symm (superpose eq914 eq2232) | exact superpose eq2232 eq914 | exact mod_symm (superpose eq2232 eq914)
  subsumption eq2233 eq57


theorem Equation332_termDefinableFromFin_Equation4541 :
    Law332.TermDefinableFromFin Law4541 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))))
    (fun G ↦ (tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)) (Term.var 1))) 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4541 G := Law4541.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) a ◇ ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) b :=
    fun a b ↦ endo4541_1 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ ((v a) ◇ (v a)))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ (a ◇ a))) = e a := fun a ↦ he.v_comp_u a
  rw [@Law332.models_iff]
  intro x y
  exact aux4541_332 h e v _ heh hvh he.idem he.comm_v hu huv hvu (fun a b ↦ rfl) x y

theorem Equation4343_termDefinableFromFin_Equation4541 :
    Law4343.TermDefinableFromFin Law4541 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))))
    (fun G ↦ (tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)) (Term.var 1))) 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4541 G := Law4541.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) a ◇ ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0)))) b :=
    fun a b ↦ endo4541_1 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ ((v a) ◇ (v a)))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ (a ◇ a))) = e a := fun a ↦ he.v_comp_u a
  rw [@Law4343.models_iff]
  intro x y
  exact aux4541_4343 h e v _ heh hvh he.idem he.comm_v hu huv hvu (fun a b ↦ rfl) x y

theorem Equation4364_termDefinableFromFin_Equation4541 :
    Law4364.TermDefinableFromFin Law4541 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))))
    (fun G ↦ (tm (Term.var 0) (Term.var 1))) 0 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation4541 G := Law4541.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))) a ◇ ufunM M (tm1 (Term.var 0) (tm1 (Term.var 0) (Term.var 0))) b :=
    fun a b ↦ endo4541_0 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huv : ∀ a : G, ((v a) ◇ ((v a) ◇ (v a))) = e a := fun a ↦ he.u_comp_v a
  have hvu : ∀ a : G, v (a ◇ (a ◇ a)) = e a := fun a ↦ he.v_comp_u a
  rw [@Law4364.models_iff]
  intro x y z
  exact aux4541_4364 h e v _ heh hvh he.idem he.comm_v hu huv hvu (fun a b ↦ rfl) x y z

end Law.MagmaLaw
