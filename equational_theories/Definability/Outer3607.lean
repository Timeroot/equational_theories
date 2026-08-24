import equational_theories.Definability.OuterIterate
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Source 3607: cells landed by an idempotent iterate applied outside the defining term

Equation 3607 `x ◇ y = z ◇ ((y ◇ z) ◇ x)` makes the unary term (xx) a magma endomorphism, so every iterate of it
distributes over `◇` and a defining term may be wrapped in one. `OuterIterate.lean` names the two
families of iterates the device can reach -- `v^[k] = u^[N k]` and `e ∘ v^[k] = u^[N k + N + 1]` --
and each cell below picks the wrapper and the base term that its target needs.

The endomorphism fact is proved from equation 3607 alone; the exponent is chosen after the magma,
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


/-- `u a = (a ◇ a)` is a magma endomorphism, from equation 3607 alone. -/
private theorem endo3607_0 [Magma G] (h : Equation3607 G) (x y : G) :
    ((x ◇ y) ◇ (x ◇ y)) = (x ◇ x) ◇ (y ◇ y) := by
  by_contra nh
  have eq6 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq7 : ((x ◇ y) ◇ (x ◇ y)) ≠ ((x ◇ x) ◇ (y ◇ y)) := mod_symm nh
  have eq8 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ X1)) := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq18 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := by first | exact superpose eq8 eq6 | exact mod_symm (superpose eq8 eq6) | exact superpose eq6 eq8 | exact mod_symm (superpose eq6 eq8)
  have eq27 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X2 ◇ X1) ◇ X3))) = (((X0 ◇ X1) ◇ X4) ◇ (X3 ◇ X2)) := by first | exact superpose eq8 eq9 | exact mod_symm (superpose eq8 eq9) | exact superpose eq9 eq8 | exact mod_symm (superpose eq9 eq8)
  have eq35 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq9 eq6 | exact mod_symm (superpose eq9 eq6) | exact superpose eq6 eq9 | exact mod_symm (superpose eq6 eq9)
  have eq57 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X4)) = (X2 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4)) := by first | exact superpose eq6 eq18 | exact mod_symm (superpose eq6 eq18) | exact superpose eq18 eq6 | exact mod_symm (superpose eq18 eq6)
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by first | exact superpose eq18 eq8 | exact mod_symm (superpose eq18 eq8) | exact superpose eq8 eq18 | exact mod_symm (superpose eq8 eq18)
  have eq66 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (((X1 ◇ X4) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq18 eq8 | exact mod_symm (superpose eq18 eq8) | exact superpose eq8 eq18 | exact mod_symm (superpose eq8 eq18)
  have eq70 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ ((X0 ◇ X3) ◇ X1))) = (((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ X3) := by first | exact superpose eq18 eq9 | exact mod_symm (superpose eq18 eq9) | exact superpose eq9 eq18 | exact mod_symm (superpose eq9 eq18)
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X4) ◇ X0))) := by first | exact superpose eq27 eq66 | exact mod_symm (superpose eq27 eq66) | exact superpose eq66 eq27 | exact mod_symm (superpose eq66 eq27)
  have eq83 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X4)) = (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X4) ◇ X2)))) := by first | exact superpose eq70 eq57 | exact mod_symm (superpose eq70 eq57) | exact superpose eq57 eq70 | exact mod_symm (superpose eq57 eq70)
  have eq90 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ (X0 ◇ X3)))) := by first | exact superpose eq65 eq79 | exact mod_symm (superpose eq65 eq79) | exact superpose eq79 eq65 | exact mod_symm (superpose eq79 eq65)
  have eq96 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ (X0 ◇ (X1 ◇ (X4 ◇ ((X3 ◇ X2) ◇ X0))))) := by first | exact superpose eq27 eq90 | exact mod_symm (superpose eq27 eq90) | exact superpose eq90 eq27 | exact mod_symm (superpose eq90 eq27)
  have eq99 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ ((X4 ◇ X3) ◇ (X1 ◇ X2))) := by first | exact superpose eq83 eq96 | exact mod_symm (superpose eq83 eq96) | exact superpose eq96 eq83 | exact mod_symm (superpose eq96 eq83)
  have eq119 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X1 ◇ X3) ◇ X0) ◇ (X2 ◇ X4))) = (X3 ◇ (X4 ◇ (X0 ◇ X1))) := by first | exact superpose eq6 eq35 | exact mod_symm (superpose eq6 eq35) | exact superpose eq35 eq6 | exact mod_symm (superpose eq35 eq6)
  have eq200 (X0 X1 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ X1))) = ((X0 ◇ X4) ◇ (X1 ◇ X3)) := by first | exact superpose eq99 eq119 | exact mod_symm (superpose eq99 eq119) | exact superpose eq119 eq99 | exact mod_symm (superpose eq119 eq99)
  have eq319 : ((x ◇ x) ◇ (y ◇ y)) ≠ (y ◇ (x ◇ (x ◇ y))) := by first | exact superpose eq65 eq7 | exact mod_symm (superpose eq65 eq7) | exact superpose eq7 eq65 | exact mod_symm (superpose eq7 eq65)
  subsumption eq319 eq200


/-- Equation 332 `x ◇ y = y ◇ (x ◇ x)` is term-definable from equation 3607 over finite magmas, via the term
`x □ y := u^[3N+1] ((x ◇ x) ◇ (y ◇ x))` with `u a = (a ◇ a)`. -/
private theorem aux3607_332 [Magma G] (h : Equation3607 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a)
    (hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v (((a ◇ a) ◇ (b ◇ a)))))))
    (x y : G) :
    (w x y) =
      (w y (w x x)) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0))))) := mod_symm (hw ..)
  have eq21 : (w x y) ≠ (w y (w x x)) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq39 (X0 : G) : (e (v X0)) = (e (v (v (X0 ◇ X0)))) := by first | exact superpose eq15 eq29 | exact mod_symm (superpose eq15 eq29) | exact superpose eq29 eq15 | exact mod_symm (superpose eq29 eq15)
  have eq64 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq30 eq17 | exact mod_symm (superpose eq30 eq17) | exact superpose eq17 eq30 | exact mod_symm (superpose eq17 eq30)
  have eq67 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq64 | exact mod_symm (superpose eq17 eq64) | exact superpose eq64 eq17 | exact mod_symm (superpose eq64 eq17)
  have eq76 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq77 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ X1)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq89 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq94 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq89 | exact mod_symm (superpose eq17 eq89) | exact superpose eq89 eq17 | exact mod_symm (superpose eq89 eq17)
  have eq110 (X0 X1 : G) : (w X0 (X1 ◇ (X0 ◇ X0))) = (e (v (v (X0 ◇ X1)))) := by first | exact superpose eq13 eq20 | exact mod_symm (superpose eq13 eq20) | exact superpose eq20 eq13 | exact mod_symm (superpose eq20 eq13)
  have eq111 (X0 X1 X2 : G) : (e ((v (v ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ X2)) = ((w X0 X1) ◇ (e X2)) := by first | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14) | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20)
  have eq112 (X0 X1 X2 : G) : (e (X2 ◇ (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0)))))) = ((e X2) ◇ (w X0 X1)) := by first | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14) | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20)
  have eq117 (X0 X1 X2 : G) : (e (X2 ◇ (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0)))))) = (e (X2 ◇ (w X0 X1))) := by first | exact superpose eq20 eq30 | exact mod_symm (superpose eq20 eq30) | exact superpose eq30 eq20 | exact mod_symm (superpose eq30 eq20)
  have eq118 (X0 X1 X2 : G) : (e ((v (v ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ X2)) = (e ((w X0 X1) ◇ X2)) := by first | exact superpose eq20 eq31 | exact mod_symm (superpose eq20 eq31) | exact superpose eq31 eq20 | exact mod_symm (superpose eq31 eq20)
  have eq120 (X0 X1 X2 : G) : ((e X2) ◇ (w X0 X1)) = (e (X2 ◇ (w X0 X1))) := by first | exact superpose eq117 eq112 | exact mod_symm (superpose eq117 eq112) | exact superpose eq112 eq117 | exact mod_symm (superpose eq112 eq117)
  have eq121 (X0 X1 X2 : G) : ((w X0 X1) ◇ (e X2)) = (e ((w X0 X1) ◇ X2)) := by first | exact superpose eq118 eq111 | exact mod_symm (superpose eq118 eq111) | exact superpose eq111 eq118 | exact mod_symm (superpose eq111 eq118)
  have eq153 (X0 : G) : (w X0 X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq39 eq20 | exact mod_symm (superpose eq39 eq20) | exact superpose eq20 eq39 | exact mod_symm (superpose eq20 eq39)
  have eq167 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq29 eq153 | exact mod_symm (superpose eq29 eq153) | exact superpose eq153 eq29 | exact mod_symm (superpose eq153 eq29)
  have eq189 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq167 eq21 | exact mod_symm (superpose eq167 eq21) | exact superpose eq21 eq167 | exact mod_symm (superpose eq21 eq167)
  have eq498 (X0 X1 : G) : (e (v (v (X0 ◇ (e X1))))) = (v (e (v (X0 ◇ X1)))) := by first | exact superpose eq67 eq17 | exact mod_symm (superpose eq67 eq17) | exact superpose eq17 eq67 | exact mod_symm (superpose eq17 eq67)
  have eq505 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (e (v (v (X0 ◇ (e X1))))) := by first | exact superpose eq17 eq498 | exact mod_symm (superpose eq17 eq498) | exact superpose eq498 eq17 | exact mod_symm (superpose eq498 eq17)
  have eq547 (X0 X1 X2 : G) : (w (w X1 X2) (e X0)) = (e (v (v (((w X1 X2) ◇ (w X1 X2)) ◇ (e (X0 ◇ (w X1 X2))))))) := by first | exact superpose eq120 eq20 | exact mod_symm (superpose eq120 eq20) | exact superpose eq20 eq120 | exact mod_symm (superpose eq20 eq120)
  have eq549 (X0 X1 X2 : G) : (w (w X1 X2) (e X0)) = (e (v (v (((w X1 X2) ◇ (w X1 X2)) ◇ (X0 ◇ (w X1 X2)))))) := by first | exact superpose eq505 eq547 | exact mod_symm (superpose eq505 eq547) | exact superpose eq547 eq505 | exact mod_symm (superpose eq547 eq505)
  have eq562 (X0 X1 X2 : G) : (w (w X1 X2) (e X0)) = (w (w X1 X2) X0) := by first | exact superpose eq20 eq549 | exact mod_symm (superpose eq20 eq549) | exact superpose eq549 eq20 | exact mod_symm (superpose eq549 eq20)
  have eq590 (X0 X1 : G) : (v (e (v (X0 ◇ X1)))) = (e (v (v ((e X0) ◇ X1)))) := by first | exact superpose eq94 eq17 | exact mod_symm (superpose eq94 eq17) | exact superpose eq17 eq94 | exact mod_symm (superpose eq17 eq94)
  have eq601 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (e (v (v ((e X0) ◇ X1)))) := by first | exact superpose eq17 eq590 | exact mod_symm (superpose eq17 eq590) | exact superpose eq590 eq17 | exact mod_symm (superpose eq590 eq17)
  have eq649 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (e (v (v (((e X2) ◇ (e X2)) ◇ (e ((w X0 X1) ◇ X2)))))) := by first | exact superpose eq121 eq20 | exact mod_symm (superpose eq121 eq20) | exact superpose eq20 eq121 | exact mod_symm (superpose eq20 eq121)
  have eq652 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (e (v (v (((e X2) ◇ (e X2)) ◇ ((w X0 X1) ◇ X2))))) := by first | exact superpose eq505 eq649 | exact mod_symm (superpose eq505 eq649) | exact superpose eq649 eq505 | exact mod_symm (superpose eq649 eq505)
  have eq667 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (e (v (v ((e (X2 ◇ X2)) ◇ ((w X0 X1) ◇ X2))))) := by first | exact superpose eq14 eq652 | exact mod_symm (superpose eq14 eq652) | exact superpose eq652 eq14 | exact mod_symm (superpose eq652 eq14)
  have eq669 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (e (v (v ((X2 ◇ X2) ◇ ((w X0 X1) ◇ X2))))) := by first | exact superpose eq601 eq667 | exact mod_symm (superpose eq601 eq667) | exact superpose eq667 eq601 | exact mod_symm (superpose eq667 eq601)
  have eq670 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq20 eq669 | exact mod_symm (superpose eq20 eq669) | exact superpose eq669 eq20 | exact mod_symm (superpose eq669 eq20)
  have eq876 (X0 X1 : G) : (w (e X0) X1) = (w (e X0) (e X1)) := by first | exact superpose eq167 eq562 | exact mod_symm (superpose eq167 eq562) | exact superpose eq562 eq167 | exact mod_symm (superpose eq562 eq167)
  have eq988 (X0 X1 X2 : G) : (w (e X2) (X0 ◇ (e X1))) = (w (e X2) (e (X0 ◇ X1))) := by first | exact superpose eq30 eq876 | exact mod_symm (superpose eq30 eq876) | exact superpose eq876 eq30 | exact mod_symm (superpose eq876 eq30)
  have eq1006 (X0 : G) : (e (e X0)) = (w (e X0) X0) := by first | exact superpose eq876 eq167 | exact mod_symm (superpose eq876 eq167) | exact superpose eq167 eq876 | exact mod_symm (superpose eq167 eq876)
  have eq1007 (X0 : G) : (e X0) = (w (e X0) X0) := by first | exact superpose eq16 eq1006 | exact mod_symm (superpose eq16 eq1006) | exact superpose eq1006 eq16 | exact mod_symm (superpose eq1006 eq16)
  have eq1019 (X0 X1 X2 : G) : (w (e X2) (X0 ◇ (e X1))) = (w (e X2) (X0 ◇ X1)) := by first | exact superpose eq876 eq988 | exact mod_symm (superpose eq876 eq988) | exact superpose eq988 eq876 | exact mod_symm (superpose eq988 eq876)
  have eq1022 (X0 X1 : G) : (e (v (v ((e X0) ◇ X1)))) = (w (e X0) (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq110 | exact mod_symm (superpose eq14 eq110) | exact superpose eq110 eq14 | exact mod_symm (superpose eq110 eq14)
  have eq1042 (X0 X1 : G) : (e (v (v ((e X0) ◇ X1)))) = (w (e X0) (X1 ◇ (X0 ◇ X0))) := by first | exact superpose eq1019 eq1022 | exact mod_symm (superpose eq1019 eq1022) | exact superpose eq1022 eq1019 | exact mod_symm (superpose eq1022 eq1019)
  have eq1047 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (w (e X0) (X1 ◇ (X0 ◇ X0))) := by first | exact superpose eq601 eq1042 | exact mod_symm (superpose eq601 eq1042) | exact superpose eq1042 eq601 | exact mod_symm (superpose eq1042 eq601)
  have eq1236 (X0 X1 : G) : (w (e X1) (e X0)) = (w X1 (e X0)) := by first | exact superpose eq1007 eq670 | exact mod_symm (superpose eq1007 eq670) | exact superpose eq670 eq1007 | exact mod_symm (superpose eq670 eq1007)
  have eq1427 (X0 X1 : G) : (w (e X0) X1) = (w X0 (e X1)) := by first | exact superpose eq1236 eq876 | exact mod_symm (superpose eq1236 eq876) | exact superpose eq876 eq1236 | exact mod_symm (superpose eq876 eq1236)
  have eq1508 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X1)) := by first | exact superpose eq76 eq13 | exact mod_symm (superpose eq76 eq13) | exact superpose eq13 eq76 | exact mod_symm (superpose eq13 eq76)
  have eq1608 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X2 ◇ X1) ◇ X3))) = (((X0 ◇ X1) ◇ X4) ◇ (X3 ◇ X2)) := by first | exact superpose eq76 eq77 | exact mod_symm (superpose eq76 eq77) | exact superpose eq77 eq76 | exact mod_symm (superpose eq77 eq76)
  have eq1617 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ (X4 ◇ X0)) ◇ X1)) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by first | exact superpose eq77 eq13 | exact mod_symm (superpose eq77 eq13) | exact superpose eq13 eq77 | exact mod_symm (superpose eq13 eq77)
  have eq1626 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq77 eq13 | exact mod_symm (superpose eq77 eq13) | exact superpose eq13 eq77 | exact mod_symm (superpose eq13 eq77)
  have eq8380 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X4)) = (X2 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4)) := by first | exact superpose eq13 eq1508 | exact mod_symm (superpose eq13 eq1508) | exact superpose eq1508 eq13 | exact mod_symm (superpose eq1508 eq13)
  have eq8398 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by first | exact superpose eq1508 eq76 | exact mod_symm (superpose eq1508 eq76) | exact superpose eq76 eq1508 | exact mod_symm (superpose eq76 eq1508)
  have eq8404 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ ((X0 ◇ X3) ◇ X1))) = (((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ X3) := by first | exact superpose eq1508 eq77 | exact mod_symm (superpose eq1508 eq77) | exact superpose eq77 eq1508 | exact mod_symm (superpose eq77 eq1508)
  have eq8432 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (((X1 ◇ X4) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq1508 eq76 | exact mod_symm (superpose eq1508 eq76) | exact superpose eq76 eq1508 | exact mod_symm (superpose eq76 eq1508)
  have eq8441 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X4) ◇ X0))) := by first | exact superpose eq1608 eq8432 | exact mod_symm (superpose eq1608 eq8432) | exact superpose eq8432 eq1608 | exact mod_symm (superpose eq8432 eq1608)
  have eq8476 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X4)) = (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X4) ◇ X2)))) := by first | exact superpose eq8404 eq8380 | exact mod_symm (superpose eq8404 eq8380) | exact superpose eq8380 eq8404 | exact mod_symm (superpose eq8380 eq8404)
  have eq8487 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ (X0 ◇ X3)))) := by first | exact superpose eq8398 eq8441 | exact mod_symm (superpose eq8398 eq8441) | exact superpose eq8441 eq8398 | exact mod_symm (superpose eq8441 eq8398)
  have eq8500 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ (X0 ◇ (X1 ◇ (X4 ◇ ((X3 ◇ X2) ◇ X0))))) := by first | exact superpose eq1608 eq8487 | exact mod_symm (superpose eq1608 eq8487) | exact superpose eq8487 eq1608 | exact mod_symm (superpose eq8487 eq1608)
  have eq8505 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ ((X4 ◇ X3) ◇ (X1 ◇ X2))) := by first | exact superpose eq8476 eq8500 | exact mod_symm (superpose eq8476 eq8500) | exact superpose eq8500 eq8476 | exact mod_symm (superpose eq8500 eq8476)
  have eq8647 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := by first | exact superpose eq8398 eq13 | exact mod_symm (superpose eq8398 eq13) | exact superpose eq13 eq8398 | exact mod_symm (superpose eq13 eq8398)
  have eq8657 (X0 X1 : G) : (w X0 X1) = (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by first | exact superpose eq8398 eq20 | exact mod_symm (superpose eq8398 eq20) | exact superpose eq20 eq8398 | exact mod_symm (superpose eq20 eq8398)
  have eq8667 (X0 X1 X2 : G) : (w (X1 ◇ X0) X2) = (e (v (v ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X1 ◇ X0)))))) := by first | exact superpose eq8398 eq20 | exact mod_symm (superpose eq8398 eq20) | exact superpose eq20 eq8398 | exact mod_symm (superpose eq20 eq8398)
  have eq8698 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by first | exact superpose eq8398 eq13 | exact mod_symm (superpose eq8398 eq13) | exact superpose eq13 eq8398 | exact mod_symm (superpose eq13 eq8398)
  have eq8731 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by first | exact superpose eq8398 eq13 | exact mod_symm (superpose eq8398 eq13) | exact superpose eq13 eq8398 | exact mod_symm (superpose eq13 eq8398)
  have eq8759 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0))) := by first | exact superpose eq1617 eq8698 | exact mod_symm (superpose eq1617 eq8698) | exact superpose eq8698 eq1617 | exact mod_symm (superpose eq8698 eq1617)
  have eq8777 (X0 X1 X2 : G) : (w (X1 ◇ X0) X2) = (e (v (v ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))))) := by first | exact superpose eq8398 eq8667 | exact mod_symm (superpose eq8398 eq8667) | exact superpose eq8667 eq8398 | exact mod_symm (superpose eq8667 eq8398)
  have eq8873 (X0 X2 X3 : G) : (X3 ◇ X2) = (((X3 ◇ X0) ◇ X0) ◇ X2) := by first | exact superpose eq8505 eq8759 | exact mod_symm (superpose eq8505 eq8759) | exact superpose eq8759 eq8505 | exact mod_symm (superpose eq8759 eq8505)
  have eq8880 (X0 X1 X2 : G) : (w (X1 ◇ X0) X2) = (e (v (v ((X0 ◇ X2) ◇ X1)))) := by first | exact superpose eq8731 eq8777 | exact mod_symm (superpose eq8731 eq8777) | exact superpose eq8777 eq8731 | exact mod_symm (superpose eq8777 eq8731)
  have eq9276 (X0 X1 : G) : (e (v (v ((X0 ◇ X0) ◇ X1)))) = (w X0 (X1 ◇ X0)) := by first | exact superpose eq8647 eq20 | exact mod_symm (superpose eq8647 eq20) | exact superpose eq20 eq8647 | exact mod_symm (superpose eq20 eq8647)
  have eq9283 (X0 X1 : G) : (e ((X0 ◇ X1) ◇ X1)) = (e (v (((X0 ◇ X1) ◇ X1) ◇ X0))) := by first | exact superpose eq8647 eq29 | exact mod_symm (superpose eq8647 eq29) | exact superpose eq29 eq8647 | exact mod_symm (superpose eq29 eq8647)
  have eq9430 (X0 X1 : G) : (e (v (X0 ◇ X0))) = (e ((X0 ◇ X1) ◇ X1)) := by first | exact superpose eq8873 eq9283 | exact mod_symm (superpose eq8873 eq9283) | exact superpose eq9283 eq8873 | exact mod_symm (superpose eq9283 eq8873)
  have eq9436 (X0 X1 : G) : (w X0 (X1 ◇ X0)) = (w (X1 ◇ X0) X0) := by first | exact superpose eq8880 eq9276 | exact mod_symm (superpose eq8880 eq9276) | exact superpose eq9276 eq8880 | exact mod_symm (superpose eq9276 eq8880)
  have eq9506 (X0 X1 : G) : (e X0) = (e ((X0 ◇ X1) ◇ X1)) := by first | exact superpose eq29 eq9430 | exact mod_symm (superpose eq29 eq9430) | exact superpose eq9430 eq29 | exact mod_symm (superpose eq9430 eq29)
  have eq10026 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X3 ◇ ((X4 ◇ X1) ◇ (X3 ◇ X4))) := by first | exact superpose eq1626 eq1626 | exact mod_symm (superpose eq1626 eq1626) | exact superpose eq1626 eq1626 | exact mod_symm (superpose eq1626 eq1626)
  have eq10247 (X0 X1 X2 X4 : G) : ((X1 ◇ X4) ◇ X4) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by first | exact superpose eq8505 eq10026 | exact mod_symm (superpose eq8505 eq10026) | exact superpose eq10026 eq8505 | exact mod_symm (superpose eq10026 eq8505)
  have eq10335 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X4) ◇ X4) := by first | exact superpose eq8731 eq10247 | exact mod_symm (superpose eq8731 eq10247) | exact superpose eq10247 eq8731 | exact mod_symm (superpose eq10247 eq8731)
  have eq10780 (X0 X1 X2 X3 : G) : ((e (X0 ◇ (w X1 X2))) ◇ (w X1 X2)) = (((e X0) ◇ X3) ◇ X3) := by first | exact superpose eq120 eq10335 | exact mod_symm (superpose eq120 eq10335) | exact superpose eq10335 eq120 | exact mod_symm (superpose eq10335 eq120)
  have eq10913 (X0 X1 X2 : G) : (w (e X2) ((X0 ◇ X1) ◇ X1)) = (e (v (v (X2 ◇ (X0 ◇ (X2 ◇ X2)))))) := by first | exact superpose eq10335 eq1047 | exact mod_symm (superpose eq10335 eq1047) | exact superpose eq1047 eq10335 | exact mod_symm (superpose eq1047 eq10335)
  have eq10915 (X0 X1 X2 : G) : (e (v (v (X2 ◇ (X0 ◇ (X2 ◇ X2)))))) = (w X2 ((X0 ◇ X1) ◇ X1)) := by first | exact superpose eq10335 eq110 | exact mod_symm (superpose eq10335 eq110) | exact superpose eq110 eq10335 | exact mod_symm (superpose eq110 eq10335)
  have eq10952 (X0 X1 X2 : G) : (w X2 ((X0 ◇ X1) ◇ X1)) = (w X2 X0) := by first | exact superpose eq8657 eq10915 | exact mod_symm (superpose eq8657 eq10915) | exact superpose eq10915 eq8657 | exact mod_symm (superpose eq10915 eq8657)
  have eq10954 (X0 X1 X2 : G) : (w (e X2) ((X0 ◇ X1) ◇ X1)) = (w X2 X0) := by first | exact superpose eq8657 eq10913 | exact mod_symm (superpose eq8657 eq10913) | exact superpose eq10913 eq8657 | exact mod_symm (superpose eq10913 eq8657)
  have eq11061 (X0 X1 X2 X3 : G) : (e ((X0 ◇ (w X1 X2)) ◇ (w X1 X2))) = (((e X0) ◇ X3) ◇ X3) := by first | exact superpose eq120 eq10780 | exact mod_symm (superpose eq120 eq10780) | exact superpose eq10780 eq120 | exact mod_symm (superpose eq10780 eq120)
  have eq11120 (X0 X2 : G) : (w X2 X0) = (w (e X2) X0) := by first | exact superpose eq10952 eq10954 | exact mod_symm (superpose eq10952 eq10954) | exact superpose eq10954 eq10952 | exact mod_symm (superpose eq10954 eq10952)
  have eq11180 (X0 X3 : G) : (e X0) = (((e X0) ◇ X3) ◇ X3) := by first | exact superpose eq9506 eq11061 | exact mod_symm (superpose eq9506 eq11061) | exact superpose eq11061 eq9506 | exact mod_symm (superpose eq11061 eq9506)
  have eq11547 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq11120 eq1427 | exact mod_symm (superpose eq11120 eq1427) | exact superpose eq1427 eq11120 | exact mod_symm (superpose eq1427 eq11120)
  have eq12240 : (w x y) ≠ (w y x) := by first | exact superpose eq11547 eq189 | exact mod_symm (superpose eq11547 eq189) | exact superpose eq189 eq11547 | exact mod_symm (superpose eq189 eq11547)
  have eq19448 (X0 X1 : G) : (w (e X0) X1) = (w X1 (e X0)) := by first | exact superpose eq11180 eq9436 | exact mod_symm (superpose eq11180 eq9436) | exact superpose eq9436 eq11180 | exact mod_symm (superpose eq9436 eq11180)
  have eq19522 (X0 X1 : G) : (w (e X0) X1) = (w X1 X0) := by first | exact superpose eq11547 eq19448 | exact mod_symm (superpose eq11547 eq19448) | exact superpose eq19448 eq11547 | exact mod_symm (superpose eq19448 eq11547)
  have eq20119 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq19522 eq11120 | exact mod_symm (superpose eq19522 eq11120) | exact superpose eq11120 eq19522 | exact mod_symm (superpose eq11120 eq19522)
  have eq20740 : (w x y) ≠ (w x y) := by first | exact superpose eq20119 eq12240 | exact mod_symm (superpose eq20119 eq12240) | exact superpose eq12240 eq20119 | exact mod_symm (superpose eq12240 eq20119)
  first | exact eq20740 rfl | exact eq20740 _ rfl | exact eq20740 _ _ rfl | exact eq20740 _ _ _ rfl


/-- Equation 3342 `x ◇ y = y ◇ (x ◇ (x ◇ x))` is term-definable from equation 3607 over finite magmas, via the term
`x □ y := u^[4N+1] ((x ◇ (x ◇ y)) ◇ y)` with `u a = (a ◇ a)`. -/
private theorem aux3607_3342 [Magma G] (h : Equation3607 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a)
    (hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v (v (((a ◇ (a ◇ b)) ◇ b)))))))
    (x y : G) :
    (w x y) =
      (w y (w x (w x x))) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) := mod_symm (hw ..)
  have eq21 : (w x y) ≠ (w y (w x (w x x))) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq33 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq35 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq36 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq37 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq39 (X0 : G) : (e (v X0)) = (e (v (v (X0 ◇ X0)))) := by first | exact superpose eq15 eq29 | exact mod_symm (superpose eq15 eq29) | exact superpose eq29 eq15 | exact mod_symm (superpose eq29 eq15)
  have eq62 (X0 X1 X2 : G) : (e (X2 ◇ (X0 ◇ (e X1)))) = ((e X2) ◇ (e (X0 ◇ X1))) := by first | exact superpose eq30 eq14 | exact mod_symm (superpose eq30 eq14) | exact superpose eq14 eq30 | exact mod_symm (superpose eq14 eq30)
  have eq68 (X0 X1 X2 : G) : (e (X2 ◇ (X0 ◇ (e X1)))) = (e (X2 ◇ (X0 ◇ X1))) := by first | exact superpose eq14 eq62 | exact mod_symm (superpose eq14 eq62) | exact superpose eq62 eq14 | exact mod_symm (superpose eq62 eq14)
  have eq74 (X0 X1 X2 : G) : (X2 ◇ (v X0)) = ((v X1) ◇ ((v (X0 ◇ X1)) ◇ X2)) := by first | exact superpose eq15 eq13 | exact mod_symm (superpose eq15 eq13) | exact superpose eq13 eq15 | exact mod_symm (superpose eq13 eq15)
  have eq75 (X0 X1 : G) : (X1 ◇ (v (e X0))) = ((v (e X0)) ◇ ((e X0) ◇ X1)) := by first | exact superpose eq18 eq13 | exact mod_symm (superpose eq18 eq13) | exact superpose eq13 eq18 | exact mod_symm (superpose eq13 eq18)
  have eq76 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq77 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ X1)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq78 (X0 X1 : G) : (X1 ◇ (e (v X0))) = ((e (v X0)) ◇ ((e X0) ◇ X1)) := by first | exact superpose eq17 eq75 | exact mod_symm (superpose eq17 eq75) | exact superpose eq75 eq17 | exact mod_symm (superpose eq75 eq17)
  have eq89 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq94 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq89 | exact mod_symm (superpose eq17 eq89) | exact superpose eq89 eq17 | exact mod_symm (superpose eq89 eq17)
  have eq103 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (v (v (((e X0) ◇ (e (X0 ◇ X1))) ◇ (e X1)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq104 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (v (((v X0) ◇ (v (X0 ◇ X1))) ◇ (v X1)))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq106 (X0 X1 X2 : G) : (w X2 ((X1 ◇ X2) ◇ X0)) = (e (v (v (v ((X2 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)))))) := by first | exact superpose eq13 eq20 | exact mod_symm (superpose eq13 eq20) | exact superpose eq20 eq13 | exact mod_symm (superpose eq20 eq13)
  have eq110 (X0 X1 : G) : (e (v (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq119 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (v ((v (X0 ◇ (X0 ◇ X1))) ◇ (v X1)))))) := by first | exact superpose eq15 eq104 | exact mod_symm (superpose eq15 eq104) | exact superpose eq104 eq15 | exact mod_symm (superpose eq104 eq15)
  have eq120 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (v (v ((e (X0 ◇ (X0 ◇ X1))) ◇ (e X1)))))) := by first | exact superpose eq14 eq103 | exact mod_symm (superpose eq14 eq103) | exact superpose eq103 eq14 | exact mod_symm (superpose eq103 eq14)
  have eq122 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq15 eq119 | exact mod_symm (superpose eq15 eq119) | exact superpose eq119 eq15 | exact mod_symm (superpose eq119 eq15)
  have eq123 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (v (v (e ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq14 eq120 | exact mod_symm (superpose eq14 eq120) | exact superpose eq120 eq14 | exact mod_symm (superpose eq120 eq14)
  have eq125 (X0 X1 : G) : (w (v X0) (v X1)) = (v (w X0 X1)) := by first | exact superpose eq110 eq122 | exact mod_symm (superpose eq110 eq122) | exact superpose eq122 eq110 | exact mod_symm (superpose eq122 eq110)
  have eq126 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (v (e (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq17 eq123 | exact mod_symm (superpose eq17 eq123) | exact superpose eq123 eq17 | exact mod_symm (superpose eq123 eq17)
  have eq128 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (e (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq17 eq126 | exact mod_symm (superpose eq17 eq126) | exact superpose eq126 eq17 | exact mod_symm (superpose eq126 eq17)
  have eq130 (X0 X1 : G) : (w (e X0) (e X1)) = (e (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq17 eq128 | exact mod_symm (superpose eq17 eq128) | exact superpose eq128 eq17 | exact mod_symm (superpose eq128 eq17)
  have eq132 (X0 X1 : G) : (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = (w (e X0) (e X1)) := by first | exact superpose eq16 eq130 | exact mod_symm (superpose eq16 eq130) | exact superpose eq130 eq16 | exact mod_symm (superpose eq130 eq16)
  have eq134 (X0 X1 : G) : (w X0 X1) = (w (e X0) (e X1)) := by first | exact superpose eq20 eq132 | exact mod_symm (superpose eq20 eq132) | exact superpose eq132 eq20 | exact mod_symm (superpose eq132 eq20)
  have eq142 (X0 X1 X2 : G) : (w (X0 ◇ (e X1)) X2) = (w (e (X0 ◇ X1)) (e X2)) := by first | exact superpose eq30 eq134 | exact mod_symm (superpose eq30 eq134) | exact superpose eq134 eq30 | exact mod_symm (superpose eq134 eq30)
  have eq143 (X0 X1 X2 : G) : (w (e (X0 ◇ X1)) (e X2)) = (w ((e X0) ◇ X1) X2) := by first | exact superpose eq31 eq134 | exact mod_symm (superpose eq31 eq134) | exact superpose eq134 eq31 | exact mod_symm (superpose eq134 eq31)
  have eq144 (X0 X1 : G) : (w (e X0) (e X1)) = (w (e X0) X1) := by first | exact superpose eq16 eq134 | exact mod_symm (superpose eq16 eq134) | exact superpose eq134 eq16 | exact mod_symm (superpose eq134 eq16)
  have eq148 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w (e X2) (e (X0 ◇ X1))) := by first | exact superpose eq30 eq134 | exact mod_symm (superpose eq30 eq134) | exact superpose eq134 eq30 | exact mod_symm (superpose eq134 eq30)
  have eq149 (X0 X1 X2 : G) : (w (e X2) (e (X0 ◇ X1))) = (w X2 ((e X0) ◇ X1)) := by first | exact superpose eq31 eq134 | exact mod_symm (superpose eq31 eq134) | exact superpose eq134 eq31 | exact mod_symm (superpose eq134 eq31)
  have eq150 (X0 X1 : G) : (w X1 (e X0)) = (w (e X1) (e X0)) := by first | exact superpose eq16 eq134 | exact mod_symm (superpose eq16 eq134) | exact superpose eq134 eq16 | exact mod_symm (superpose eq134 eq16)
  have eq151 (X0 X1 : G) : (w (e X1) (e X0)) = (w X1 (v (X0 ◇ X0))) := by first | exact superpose eq29 eq134 | exact mod_symm (superpose eq29 eq134) | exact superpose eq134 eq29 | exact mod_symm (superpose eq134 eq29)
  have eq156 (X0 X1 : G) : (w X1 (v (X0 ◇ X0))) = (w X1 X0) := by first | exact superpose eq134 eq151 | exact mod_symm (superpose eq134 eq151) | exact superpose eq151 eq134 | exact mod_symm (superpose eq151 eq134)
  have eq157 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq134 eq150 | exact mod_symm (superpose eq134 eq150) | exact superpose eq150 eq134 | exact mod_symm (superpose eq150 eq134)
  have eq158 (X0 X1 X2 : G) : (w X2 ((e X0) ◇ X1)) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq134 eq149 | exact mod_symm (superpose eq134 eq149) | exact superpose eq149 eq134 | exact mod_symm (superpose eq149 eq134)
  have eq159 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq134 eq148 | exact mod_symm (superpose eq134 eq148) | exact superpose eq148 eq134 | exact mod_symm (superpose eq148 eq134)
  have eq162 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq134 eq144 | exact mod_symm (superpose eq134 eq144) | exact superpose eq144 eq134 | exact mod_symm (superpose eq144 eq134)
  have eq163 (X0 X1 X2 : G) : (w ((e X0) ◇ X1) X2) = (w (X0 ◇ X1) X2) := by first | exact superpose eq134 eq143 | exact mod_symm (superpose eq134 eq143) | exact superpose eq143 eq134 | exact mod_symm (superpose eq143 eq134)
  have eq164 (X0 X1 X2 : G) : (w (X0 ◇ (e X1)) X2) = (w (X0 ◇ X1) X2) := by first | exact superpose eq134 eq142 | exact mod_symm (superpose eq134 eq142) | exact superpose eq142 eq134 | exact mod_symm (superpose eq142 eq134)
  have eq176 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w (e X0) (v X1)) := by first | exact superpose eq19 eq125 | exact mod_symm (superpose eq19 eq125) | exact superpose eq125 eq19 | exact mod_symm (superpose eq125 eq19)
  have eq178 (X0 X1 : G) : (v (w X1 ((e X0) ◇ (e X0)))) = (w (v X1) (e X0)) := by first | exact superpose eq19 eq125 | exact mod_symm (superpose eq19 eq125) | exact superpose eq125 eq19 | exact mod_symm (superpose eq125 eq19)
  have eq180 (X0 X1 : G) : (v (w X1 ((e X0) ◇ (e X0)))) = (w (v X1) X0) := by first | exact superpose eq157 eq178 | exact mod_symm (superpose eq157 eq178) | exact superpose eq178 eq157 | exact mod_symm (superpose eq178 eq157)
  have eq182 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w X0 (v X1)) := by first | exact superpose eq162 eq176 | exact mod_symm (superpose eq162 eq176) | exact superpose eq176 eq162 | exact mod_symm (superpose eq176 eq162)
  have eq184 (X0 X1 : G) : (w (v X1) X0) = (v (w X1 (X0 ◇ (e X0)))) := by first | exact superpose eq158 eq180 | exact mod_symm (superpose eq158 eq180) | exact superpose eq180 eq158 | exact mod_symm (superpose eq180 eq158)
  have eq186 (X0 X1 : G) : (w X0 (v X1)) = (v (w (X0 ◇ (e X0)) X1)) := by first | exact superpose eq163 eq182 | exact mod_symm (superpose eq163 eq182) | exact superpose eq182 eq163 | exact mod_symm (superpose eq182 eq163)
  have eq188 (X0 X1 : G) : (w (v X1) X0) = (v (w X1 (X0 ◇ X0))) := by first | exact superpose eq159 eq184 | exact mod_symm (superpose eq159 eq184) | exact superpose eq184 eq159 | exact mod_symm (superpose eq184 eq159)
  have eq189 (X0 X1 : G) : (w X0 (v X1)) = (v (w (X0 ◇ X0) X1)) := by first | exact superpose eq164 eq186 | exact mod_symm (superpose eq164 eq186) | exact superpose eq186 eq164 | exact mod_symm (superpose eq186 eq164)
  have eq230 (X0 : G) : (e (v (v X0))) = (e (v (v (v (X0 ◇ X0))))) := by first | exact superpose eq15 eq39 | exact mod_symm (superpose eq15 eq39) | exact superpose eq39 eq15 | exact mod_symm (superpose eq39 eq15)
  have eq342 (X0 X1 : G) : ((v (e X0)) ◇ (e X1)) = (v (e (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq14 eq36 | exact mod_symm (superpose eq14 eq36) | exact superpose eq36 eq14 | exact mod_symm (superpose eq36 eq14)
  have eq350 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e (X1 ◇ X1))))) = ((v X2) ◇ ((v X0) ◇ (e X1))) := by first | exact superpose eq36 eq15 | exact mod_symm (superpose eq36 eq15) | exact superpose eq15 eq36 | exact mod_symm (superpose eq15 eq36)
  have eq367 (X0 X1 : G) : ((v (e X0)) ◇ (e X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq17 eq342 | exact mod_symm (superpose eq17 eq342) | exact superpose eq342 eq17 | exact mod_symm (superpose eq342 eq17)
  have eq382 (X0 X1 : G) : ((e (v X0)) ◇ (e X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq17 eq367 | exact mod_symm (superpose eq17 eq367) | exact superpose eq367 eq17 | exact mod_symm (superpose eq367 eq17)
  have eq389 (X0 X1 : G) : (e ((v X0) ◇ X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq14 eq382 | exact mod_symm (superpose eq14 eq382) | exact superpose eq382 eq14 | exact mod_symm (superpose eq382 eq14)
  have eq433 (X0 X1 X2 : G) : (v (X2 ◇ ((e (X0 ◇ X0)) ◇ X1))) = ((v X2) ◇ ((e X0) ◇ (v X1))) := by first | exact superpose eq37 eq15 | exact mod_symm (superpose eq37 eq15) | exact superpose eq15 eq37 | exact mod_symm (superpose eq15 eq37)
  have eq439 (X0 X1 X2 : G) : (v (w X2 ((e (X0 ◇ X0)) ◇ X1))) = (w (v X2) ((e X0) ◇ (v X1))) := by first | exact superpose eq37 eq125 | exact mod_symm (superpose eq37 eq125) | exact superpose eq125 eq37 | exact mod_symm (superpose eq125 eq37)
  have eq440 (X0 X1 X2 : G) : (v (w X2 ((e (X0 ◇ X0)) ◇ X1))) = (w (v X2) (X0 ◇ (v X1))) := by first | exact superpose eq158 eq439 | exact mod_symm (superpose eq158 eq439) | exact superpose eq439 eq158 | exact mod_symm (superpose eq439 eq158)
  have eq458 (X0 X1 X2 : G) : (w (v X2) (X0 ◇ (v X1))) = (v (w X2 ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq158 eq440 | exact mod_symm (superpose eq158 eq440) | exact superpose eq440 eq158 | exact mod_symm (superpose eq440 eq158)
  have eq833 (X0 X1 X2 : G) : (X2 ◇ (v (v X0))) = ((v (v X1)) ◇ ((v (v (X0 ◇ X1))) ◇ X2)) := by first | exact superpose eq15 eq74 | exact mod_symm (superpose eq15 eq74) | exact superpose eq74 eq15 | exact mod_symm (superpose eq74 eq15)
  have eq1156 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X1)) := by first | exact superpose eq76 eq13 | exact mod_symm (superpose eq76 eq13) | exact superpose eq13 eq76 | exact mod_symm (superpose eq13 eq76)
  have eq1247 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X2 ◇ X1) ◇ X3))) = (((X0 ◇ X1) ◇ X4) ◇ (X3 ◇ X2)) := by first | exact superpose eq76 eq77 | exact mod_symm (superpose eq76 eq77) | exact superpose eq77 eq76 | exact mod_symm (superpose eq77 eq76)
  have eq1265 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq77 eq13 | exact mod_symm (superpose eq77 eq13) | exact superpose eq13 eq77 | exact mod_symm (superpose eq13 eq77)
  have eq2172 (X0 X1 : G) : (v (e (v (X0 ◇ X1)))) = (e (v (v ((e X0) ◇ X1)))) := by first | exact superpose eq94 eq17 | exact mod_symm (superpose eq94 eq17) | exact superpose eq17 eq94 | exact mod_symm (superpose eq17 eq94)
  have eq2199 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (e (v (v ((e X0) ◇ X1)))) := by first | exact superpose eq17 eq2172 | exact mod_symm (superpose eq17 eq2172) | exact superpose eq2172 eq17 | exact mod_symm (superpose eq2172 eq17)
  have eq2451 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ (e (X0 ◇ X1)))) = (w X2 (X3 ◇ ((e X0) ◇ X1))) := by first | exact superpose eq31 eq159 | exact mod_symm (superpose eq31 eq159) | exact superpose eq159 eq31 | exact mod_symm (superpose eq159 eq31)
  have eq2518 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((e X0) ◇ X1))) = (w X2 (X3 ◇ (X0 ◇ X1))) := by first | exact superpose eq159 eq2451 | exact mod_symm (superpose eq159 eq2451) | exact superpose eq2451 eq159 | exact mod_symm (superpose eq2451 eq159)
  have eq3328 (X0 X1 X2 X3 X4 : G) : (w X3 (X4 ◇ (X0 ◇ (X1 ◇ (e X2))))) = (w X3 (X4 ◇ (e (X0 ◇ (X1 ◇ X2))))) := by first | exact superpose eq68 eq159 | exact mod_symm (superpose eq68 eq159) | exact superpose eq159 eq68 | exact mod_symm (superpose eq159 eq68)
  have eq3339 (X0 X1 X2 X3 X4 : G) : (w X3 (X4 ◇ (X0 ◇ (X1 ◇ (e X2))))) = (w X3 (X4 ◇ (X0 ◇ (X1 ◇ X2)))) := by first | exact superpose eq159 eq3328 | exact mod_symm (superpose eq159 eq3328) | exact superpose eq3328 eq159 | exact mod_symm (superpose eq3328 eq159)
  have eq4471 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by first | exact superpose eq1156 eq76 | exact mod_symm (superpose eq1156 eq76) | exact superpose eq76 eq1156 | exact mod_symm (superpose eq76 eq1156)
  have eq4587 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ ((v X0) ◇ X2)) := by first | exact superpose eq15 eq4471 | exact mod_symm (superpose eq15 eq4471) | exact superpose eq4471 eq15 | exact mod_symm (superpose eq4471 eq15)
  have eq4692 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := by first | exact superpose eq4471 eq13 | exact mod_symm (superpose eq4471 eq13) | exact superpose eq13 eq4471 | exact mod_symm (superpose eq13 eq4471)
  have eq4766 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by first | exact superpose eq4471 eq13 | exact mod_symm (superpose eq4471 eq13) | exact superpose eq13 eq4471 | exact mod_symm (superpose eq13 eq4471)
  have eq5158 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X2) := by first | exact superpose eq4692 eq76 | exact mod_symm (superpose eq4692 eq76) | exact superpose eq76 eq4692 | exact mod_symm (superpose eq76 eq4692)
  have eq5159 (X0 X1 : G) : (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = (w X0 ((X1 ◇ X0) ◇ X0)) := by first | exact superpose eq4692 eq106 | exact mod_symm (superpose eq4692 eq106) | exact superpose eq106 eq4692 | exact mod_symm (superpose eq106 eq4692)
  have eq5213 (X0 X1 X2 : G) : (w X0 ((X1 ◇ X2) ◇ X2)) = (e (v (v (v ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X1))))) := by first | exact superpose eq4692 eq20 | exact mod_symm (superpose eq4692 eq20) | exact superpose eq20 eq4692 | exact mod_symm (superpose eq20 eq4692)
  have eq5260 (X0 X1 X2 : G) : (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = (w X0 ((X1 ◇ X2) ◇ X2)) := by first | exact superpose eq4692 eq5213 | exact mod_symm (superpose eq4692 eq5213) | exact superpose eq5213 eq4692 | exact mod_symm (superpose eq5213 eq4692)
  have eq5312 (X0 X1 : G) : (w X0 X1) = (w X0 ((X1 ◇ X0) ◇ X0)) := by first | exact superpose eq20 eq5159 | exact mod_symm (superpose eq20 eq5159) | exact superpose eq5159 eq20 | exact mod_symm (superpose eq5159 eq20)
  have eq5341 (X0 X1 X2 : G) : (w X0 X1) = (w X0 ((X1 ◇ X2) ◇ X2)) := by first | exact superpose eq20 eq5260 | exact mod_symm (superpose eq20 eq5260) | exact superpose eq5260 eq20 | exact mod_symm (superpose eq5260 eq20)
  have eq5855 (X0 X1 X2 : G) : (w X2 (X2 ◇ X1)) = (e (v (v (v ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X1)))))) := by first | exact superpose eq1265 eq20 | exact mod_symm (superpose eq1265 eq20) | exact superpose eq20 eq1265 | exact mod_symm (superpose eq20 eq1265)
  have eq5867 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (v (X2 ◇ X3))))) = (((v X3) ◇ X1) ◇ (v X2)) := by first | exact superpose eq1265 eq74 | exact mod_symm (superpose eq1265 eq74) | exact superpose eq74 eq1265 | exact mod_symm (superpose eq74 eq1265)
  have eq5899 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X5) = (((X4 ◇ X5) ◇ X3) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by first | exact superpose eq1265 eq76 | exact mod_symm (superpose eq1265 eq76) | exact superpose eq76 eq1265 | exact mod_symm (superpose eq76 eq1265)
  have eq5913 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X5) = (X4 ◇ (X3 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X5) ◇ X0))) := by first | exact superpose eq1247 eq5899 | exact mod_symm (superpose eq1247 eq5899) | exact superpose eq5899 eq1247 | exact mod_symm (superpose eq5899 eq1247)
  have eq5943 (X0 X1 X2 : G) : (w X2 (X2 ◇ X1)) = (e (v (v (v (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))))))) := by first | exact superpose eq4471 eq5855 | exact mod_symm (superpose eq4471 eq5855) | exact superpose eq5855 eq4471 | exact mod_symm (superpose eq5855 eq4471)
  have eq6035 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X5) = (X4 ◇ (X3 ◇ (X2 ◇ (X5 ◇ X1)))) := by first | exact superpose eq77 eq5913 | exact mod_symm (superpose eq77 eq5913) | exact superpose eq5913 eq77 | exact mod_symm (superpose eq5913 eq77)
  have eq6047 (X0 X1 X2 : G) : (w X2 (X2 ◇ X1)) = (e (v (v (v (X1 ◇ ((X1 ◇ X0) ◇ X0)))))) := by first | exact superpose eq4766 eq5943 | exact mod_symm (superpose eq4766 eq5943) | exact superpose eq5943 eq4766 | exact mod_symm (superpose eq5943 eq4766)
  have eq6090 (X1 X2 : G) : (w X2 (X2 ◇ X1)) = (e (v (v (v (X1 ◇ X1))))) := by first | exact superpose eq4692 eq6047 | exact mod_symm (superpose eq4692 eq6047) | exact superpose eq6047 eq4692 | exact mod_symm (superpose eq6047 eq4692)
  have eq6116 (X1 X2 : G) : (e (v (v X1))) = (w X2 (X2 ◇ X1)) := by first | exact superpose eq230 eq6090 | exact mod_symm (superpose eq230 eq6090) | exact superpose eq6090 eq230 | exact mod_symm (superpose eq6090 eq230)
  have eq6157 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (e (v (v (X2 ◇ (X3 ◇ X1))))) := by first | exact superpose eq1265 eq6116 | exact mod_symm (superpose eq1265 eq6116) | exact superpose eq6116 eq1265 | exact mod_symm (superpose eq6116 eq1265)
  have eq6162 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (w (e (v X1)) (X0 ◇ (e (v X1)))) := by first | exact superpose eq78 eq6116 | exact mod_symm (superpose eq78 eq6116) | exact superpose eq6116 eq78 | exact mod_symm (superpose eq6116 eq78)
  have eq6171 (X0 X1 X2 : G) : (w (v X2) (X0 ◇ (v X1))) = (e (v (v ((v (X1 ◇ X2)) ◇ X0)))) := by first | exact superpose eq74 eq6116 | exact mod_symm (superpose eq74 eq6116) | exact superpose eq6116 eq74 | exact mod_symm (superpose eq6116 eq74)
  have eq6238 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (w (v X1) (X0 ◇ (e (v X1)))) := by first | exact superpose eq162 eq6162 | exact mod_symm (superpose eq162 eq6162) | exact superpose eq6162 eq162 | exact mod_symm (superpose eq6162 eq162)
  have eq6253 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (w (v X1) (X0 ◇ (v X1))) := by first | exact superpose eq159 eq6238 | exact mod_symm (superpose eq159 eq6238) | exact superpose eq6238 eq159 | exact mod_symm (superpose eq6238 eq159)
  have eq6264 (X0 X1 : G) : (e (v (v (X1 ◇ X0)))) = (w (v X1) (X0 ◇ (v X1))) := by first | exact superpose eq2199 eq6253 | exact mod_symm (superpose eq2199 eq6253) | exact superpose eq6253 eq2199 | exact mod_symm (superpose eq6253 eq2199)
  have eq10452 (X0 X1 : G) : (e ((v (v (v X1))) ◇ (v (v (X0 ◇ X1))))) = (e (v ((v (v (X0 ◇ X1))) ◇ (v (v X0))))) := by first | exact superpose eq833 eq389 | exact mod_symm (superpose eq833 eq389) | exact superpose eq389 eq833 | exact mod_symm (superpose eq389 eq833)
  have eq10510 (X0 X1 : G) : (e ((v (v (v X1))) ◇ (v (v (X0 ◇ X1))))) = (e (v (v ((v (X0 ◇ X1)) ◇ (v X0))))) := by first | exact superpose eq15 eq10452 | exact mod_symm (superpose eq15 eq10452) | exact superpose eq10452 eq15 | exact mod_symm (superpose eq10452 eq15)
  have eq10593 (X0 X1 : G) : (e ((v (v (v X1))) ◇ (v (v (X0 ◇ X1))))) = (w (v X1) ((v X0) ◇ (v X0))) := by first | exact superpose eq6171 eq10510 | exact mod_symm (superpose eq6171 eq10510) | exact superpose eq10510 eq6171 | exact mod_symm (superpose eq10510 eq6171)
  have eq10661 (X0 X1 : G) : (w (v X1) (v (X0 ◇ X0))) = (e ((v (v (v X1))) ◇ (v (v (X0 ◇ X1))))) := by first | exact superpose eq15 eq10593 | exact mod_symm (superpose eq15 eq10593) | exact superpose eq10593 eq15 | exact mod_symm (superpose eq10593 eq15)
  have eq10701 (X0 X1 : G) : (w (v X1) (v (X0 ◇ X0))) = (e (v ((v (v X1)) ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq15 eq10661 | exact mod_symm (superpose eq15 eq10661) | exact superpose eq10661 eq15 | exact mod_symm (superpose eq10661 eq15)
  have eq10727 (X0 X1 : G) : (w (v X1) (v (X0 ◇ X0))) = (e (v (v ((v X1) ◇ (X0 ◇ X1))))) := by first | exact superpose eq15 eq10701 | exact mod_symm (superpose eq15 eq10701) | exact superpose eq10701 eq15 | exact mod_symm (superpose eq10701 eq15)
  have eq10743 (X0 X1 : G) : (w (v X1) (v (X0 ◇ X0))) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq4471 eq10727 | exact mod_symm (superpose eq4471 eq10727) | exact superpose eq10727 eq4471 | exact mod_symm (superpose eq10727 eq4471)
  have eq10753 (X0 X1 : G) : (v (w X1 (X0 ◇ X0))) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq125 eq10743 | exact mod_symm (superpose eq125 eq10743) | exact superpose eq10743 eq125 | exact mod_symm (superpose eq10743 eq125)
  have eq10759 (X0 X1 : G) : (w (v X1) X0) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq188 eq10753 | exact mod_symm (superpose eq188 eq10753) | exact superpose eq10753 eq188 | exact mod_symm (superpose eq10753 eq188)
  have eq11110 (X0 X1 X2 : G) : (v (X0 ◇ X1)) = (((v (X0 ◇ X1)) ◇ X2) ◇ X2) := by first | exact superpose eq15 eq5158 | exact mod_symm (superpose eq15 eq5158) | exact superpose eq5158 eq15 | exact mod_symm (superpose eq5158 eq15)
  have eq11577 (X0 : G) : (v (w X0 X0)) = (w (v X0) (X0 ◇ (v X0))) := by first | exact superpose eq5312 eq458 | exact mod_symm (superpose eq5312 eq458) | exact superpose eq458 eq5312 | exact mod_symm (superpose eq458 eq5312)
  have eq11617 (X0 : G) : (e (v (v (X0 ◇ X0)))) = (v (w X0 X0)) := by first | exact superpose eq6264 eq11577 | exact mod_symm (superpose eq6264 eq11577) | exact superpose eq11577 eq6264 | exact mod_symm (superpose eq11577 eq6264)
  have eq11664 (X0 : G) : (e (v X0)) = (v (w X0 X0)) := by first | exact superpose eq39 eq11617 | exact mod_symm (superpose eq39 eq11617) | exact superpose eq11617 eq39 | exact mod_symm (superpose eq11617 eq39)
  have eq12075 (X0 : G) : (e (v (X0 ◇ X0))) = (w X0 (v (X0 ◇ X0))) := by first | exact superpose eq11664 eq189 | exact mod_symm (superpose eq11664 eq189) | exact superpose eq189 eq11664 | exact mod_symm (superpose eq189 eq11664)
  have eq12135 (X0 : G) : (w X0 X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq156 eq12075 | exact mod_symm (superpose eq156 eq12075) | exact superpose eq12075 eq156 | exact mod_symm (superpose eq12075 eq156)
  have eq12190 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq29 eq12135 | exact mod_symm (superpose eq29 eq12135) | exact superpose eq12135 eq29 | exact mod_symm (superpose eq12135 eq29)
  have eq12727 : (w x y) ≠ (w y (w x (e x))) := by first | exact superpose eq12190 eq21 | exact mod_symm (superpose eq12190 eq21) | exact superpose eq21 eq12190 | exact mod_symm (superpose eq21 eq12190)
  have eq12728 : (w x y) ≠ (w y (w x x)) := by first | exact superpose eq157 eq12727 | exact mod_symm (superpose eq157 eq12727) | exact superpose eq12727 eq157 | exact mod_symm (superpose eq12727 eq157)
  have eq12779 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq12190 eq12728 | exact mod_symm (superpose eq12190 eq12728) | exact superpose eq12728 eq12190 | exact mod_symm (superpose eq12728 eq12190)
  have eq12820 : (w x y) ≠ (w y x) := by first | exact superpose eq157 eq12779 | exact mod_symm (superpose eq157 eq12779) | exact superpose eq12779 eq157 | exact mod_symm (superpose eq12779 eq157)
  have eq12881 (X0 X1 X2 X3 X4 : G) : (v (X0 ◇ (X1 ◇ X2))) = ((v ((X2 ◇ ((X3 ◇ (e (X4 ◇ X4))) ◇ X0)) ◇ X1)) ◇ ((v X3) ◇ (e X4))) := by first | exact superpose eq77 eq350 | exact mod_symm (superpose eq77 eq350) | exact superpose eq350 eq77 | exact mod_symm (superpose eq350 eq77)
  have eq13020 (X0 X1 X2 X3 X4 : G) : (v (X0 ◇ (X1 ◇ X2))) = ((e X4) ◇ (v (X3 ◇ ((X2 ◇ ((X3 ◇ (e (X4 ◇ X4))) ◇ X0)) ◇ X1)))) := by first | exact superpose eq4587 eq12881 | exact mod_symm (superpose eq4587 eq12881) | exact superpose eq12881 eq4587 | exact mod_symm (superpose eq12881 eq4587)
  have eq13118 (X0 X1 X2 X3 X4 : G) : (v (X0 ◇ (X1 ◇ X2))) = ((e X4) ◇ (v (X3 ◇ ((e (X4 ◇ X4)) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0))))))) := by first | exact superpose eq6035 eq13020 | exact mod_symm (superpose eq6035 eq13020) | exact superpose eq13020 eq6035 | exact mod_symm (superpose eq13020 eq6035)
  have eq13206 (X0 X1 X2 X3 X4 : G) : (v (X0 ◇ (X1 ◇ X2))) = ((e X4) ◇ ((v X3) ◇ ((e X4) ◇ (v (X3 ◇ (X2 ◇ (X1 ◇ X0))))))) := by first | exact superpose eq433 eq13118 | exact mod_symm (superpose eq433 eq13118) | exact superpose eq13118 eq433 | exact mod_symm (superpose eq13118 eq433)
  have eq13274 (X0 X1 X2 X3 : G) : (v (X0 ◇ (X1 ◇ X2))) = (((v (X2 ◇ (X1 ◇ X0))) ◇ (v X3)) ◇ (v X3)) := by first | exact superpose eq5867 eq13206 | exact mod_symm (superpose eq5867 eq13206) | exact superpose eq13206 eq5867 | exact mod_symm (superpose eq13206 eq5867)
  have eq13327 (X0 X1 X2 : G) : (v (X0 ◇ (X1 ◇ X2))) = (v (X2 ◇ (X1 ◇ X0))) := by first | exact superpose eq11110 eq13274 | exact mod_symm (superpose eq11110 eq13274) | exact superpose eq13274 eq11110 | exact mod_symm (superpose eq13274 eq11110)
  have eq13916 (X0 X1 X2 : G) : (w X2 (e (v X1))) = (w X2 ((X0 ◇ (e (v X1))) ◇ ((e X1) ◇ X0))) := by first | exact superpose eq78 eq5341 | exact mod_symm (superpose eq78 eq5341) | exact superpose eq5341 eq78 | exact mod_symm (superpose eq5341 eq78)
  have eq13935 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ X2))) = (w X3 (X2 ◇ (X1 ◇ X0))) := by first | exact superpose eq77 eq5341 | exact mod_symm (superpose eq77 eq5341) | exact superpose eq5341 eq77 | exact mod_symm (superpose eq5341 eq77)
  have eq14043 (X0 X1 X2 : G) : (w X2 (e (v X1))) = (w X2 ((X0 ◇ (e (v X1))) ◇ (X1 ◇ X0))) := by first | exact superpose eq2518 eq13916 | exact mod_symm (superpose eq2518 eq13916) | exact superpose eq13916 eq2518 | exact mod_symm (superpose eq13916 eq2518)
  have eq14076 (X0 X1 X2 : G) : (w X2 (e (v X1))) = (w X2 (X0 ◇ (X1 ◇ (X0 ◇ (e (v X1)))))) := by first | exact superpose eq13935 eq14043 | exact mod_symm (superpose eq13935 eq14043) | exact superpose eq14043 eq13935 | exact mod_symm (superpose eq14043 eq13935)
  have eq14099 (X0 X1 X2 : G) : (w X2 (e (v X1))) = (w X2 (X0 ◇ (X1 ◇ (X0 ◇ (v X1))))) := by first | exact superpose eq3339 eq14076 | exact mod_symm (superpose eq3339 eq14076) | exact superpose eq14076 eq3339 | exact mod_symm (superpose eq14076 eq3339)
  have eq14110 (X1 X2 : G) : (w X2 (e (v X1))) = (e (v (v ((v X1) ◇ (X2 ◇ X1))))) := by first | exact superpose eq6157 eq14099 | exact mod_symm (superpose eq6157 eq14099) | exact superpose eq14099 eq6157 | exact mod_symm (superpose eq14099 eq6157)
  have eq14116 (X1 X2 : G) : (w X2 (e (v X1))) = (e (v (v (X1 ◇ (X2 ◇ (v X1)))))) := by first | exact superpose eq13327 eq14110 | exact mod_symm (superpose eq13327 eq14110) | exact superpose eq14110 eq13327 | exact mod_symm (superpose eq14110 eq13327)
  have eq14118 (X1 X2 : G) : (w (v X1) X2) = (w X2 (e (v X1))) := by first | exact superpose eq10759 eq14116 | exact mod_symm (superpose eq10759 eq14116) | exact superpose eq14116 eq10759 | exact mod_symm (superpose eq14116 eq10759)
  have eq14120 (X1 X2 : G) : (w (v X1) X2) = (w X2 (v X1)) := by first | exact superpose eq157 eq14118 | exact mod_symm (superpose eq157 eq14118) | exact superpose eq14118 eq157 | exact mod_symm (superpose eq14118 eq157)
  have eq14654 (X0 X1 : G) : (w (e X0) X1) = (w X1 (e X0)) := by first | exact superpose eq19 eq14120 | exact mod_symm (superpose eq19 eq14120) | exact superpose eq14120 eq19 | exact mod_symm (superpose eq14120 eq19)
  have eq14768 (X0 X1 : G) : (w (e X0) X1) = (w X1 X0) := by first | exact superpose eq157 eq14654 | exact mod_symm (superpose eq157 eq14654) | exact superpose eq14654 eq157 | exact mod_symm (superpose eq14654 eq157)
  have eq15220 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq14768 eq162 | exact mod_symm (superpose eq14768 eq162) | exact superpose eq162 eq14768 | exact mod_symm (superpose eq162 eq14768)
  have eq15940 : (w x y) ≠ (w x y) := by first | exact superpose eq15220 eq12820 | exact mod_symm (superpose eq15220 eq12820) | exact superpose eq12820 eq15220 | exact mod_symm (superpose eq12820 eq15220)
  first | exact eq15940 rfl | exact eq15940 _ rfl | exact eq15940 _ _ rfl | exact eq15940 _ _ _ rfl


/-- Equation 3545 `x ◇ y = y ◇ ((x ◇ x) ◇ x)` is term-definable from equation 3607 over finite magmas, via the term
`x □ y := u^[4N+1] ((x ◇ (x ◇ y)) ◇ y)` with `u a = (a ◇ a)`. -/
private theorem aux3607_3545 [Magma G] (h : Equation3607 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a)
    (hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v (v (((a ◇ (a ◇ b)) ◇ b)))))))
    (x y : G) :
    (w x y) =
      (w y (w (w x x) x)) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) := mod_symm (hw ..)
  have eq21 : (w x y) ≠ (w y (w (w x x) x)) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq33 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq35 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq36 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq37 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq39 (X0 : G) : (e (v X0)) = (e (v (v (X0 ◇ X0)))) := by first | exact superpose eq15 eq29 | exact mod_symm (superpose eq15 eq29) | exact superpose eq29 eq15 | exact mod_symm (superpose eq29 eq15)
  have eq62 (X0 X1 X2 : G) : (e (X2 ◇ (X0 ◇ (e X1)))) = ((e X2) ◇ (e (X0 ◇ X1))) := by first | exact superpose eq30 eq14 | exact mod_symm (superpose eq30 eq14) | exact superpose eq14 eq30 | exact mod_symm (superpose eq14 eq30)
  have eq68 (X0 X1 X2 : G) : (e (X2 ◇ (X0 ◇ (e X1)))) = (e (X2 ◇ (X0 ◇ X1))) := by first | exact superpose eq14 eq62 | exact mod_symm (superpose eq14 eq62) | exact superpose eq62 eq14 | exact mod_symm (superpose eq62 eq14)
  have eq74 (X0 X1 X2 : G) : (X2 ◇ (v X0)) = ((v X1) ◇ ((v (X0 ◇ X1)) ◇ X2)) := by first | exact superpose eq15 eq13 | exact mod_symm (superpose eq15 eq13) | exact superpose eq13 eq15 | exact mod_symm (superpose eq13 eq15)
  have eq75 (X0 X1 : G) : (X1 ◇ (v (e X0))) = ((v (e X0)) ◇ ((e X0) ◇ X1)) := by first | exact superpose eq18 eq13 | exact mod_symm (superpose eq18 eq13) | exact superpose eq13 eq18 | exact mod_symm (superpose eq13 eq18)
  have eq76 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq77 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ X1)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq78 (X0 X1 : G) : (X1 ◇ (e (v X0))) = ((e (v X0)) ◇ ((e X0) ◇ X1)) := by first | exact superpose eq17 eq75 | exact mod_symm (superpose eq17 eq75) | exact superpose eq75 eq17 | exact mod_symm (superpose eq75 eq17)
  have eq89 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq94 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq89 | exact mod_symm (superpose eq17 eq89) | exact superpose eq89 eq17 | exact mod_symm (superpose eq89 eq17)
  have eq103 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (v (v (((e X0) ◇ (e (X0 ◇ X1))) ◇ (e X1)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq104 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (v (((v X0) ◇ (v (X0 ◇ X1))) ◇ (v X1)))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq106 (X0 X1 X2 : G) : (w X2 ((X1 ◇ X2) ◇ X0)) = (e (v (v (v ((X2 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)))))) := by first | exact superpose eq13 eq20 | exact mod_symm (superpose eq13 eq20) | exact superpose eq20 eq13 | exact mod_symm (superpose eq20 eq13)
  have eq109 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq110 (X0 X1 : G) : (e (v (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq119 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (v ((v (X0 ◇ (X0 ◇ X1))) ◇ (v X1)))))) := by first | exact superpose eq15 eq104 | exact mod_symm (superpose eq15 eq104) | exact superpose eq104 eq15 | exact mod_symm (superpose eq104 eq15)
  have eq120 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (v (v ((e (X0 ◇ (X0 ◇ X1))) ◇ (e X1)))))) := by first | exact superpose eq14 eq103 | exact mod_symm (superpose eq14 eq103) | exact superpose eq103 eq14 | exact mod_symm (superpose eq103 eq14)
  have eq122 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq15 eq119 | exact mod_symm (superpose eq15 eq119) | exact superpose eq119 eq15 | exact mod_symm (superpose eq119 eq15)
  have eq123 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (v (v (e ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq14 eq120 | exact mod_symm (superpose eq14 eq120) | exact superpose eq120 eq14 | exact mod_symm (superpose eq120 eq14)
  have eq125 (X0 X1 : G) : (w (v X0) (v X1)) = (v (w X0 X1)) := by first | exact superpose eq110 eq122 | exact mod_symm (superpose eq110 eq122) | exact superpose eq122 eq110 | exact mod_symm (superpose eq122 eq110)
  have eq126 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (v (e (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq17 eq123 | exact mod_symm (superpose eq17 eq123) | exact superpose eq123 eq17 | exact mod_symm (superpose eq123 eq17)
  have eq128 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (e (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq17 eq126 | exact mod_symm (superpose eq17 eq126) | exact superpose eq126 eq17 | exact mod_symm (superpose eq126 eq17)
  have eq130 (X0 X1 : G) : (w (e X0) (e X1)) = (e (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := by first | exact superpose eq17 eq128 | exact mod_symm (superpose eq17 eq128) | exact superpose eq128 eq17 | exact mod_symm (superpose eq128 eq17)
  have eq132 (X0 X1 : G) : (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = (w (e X0) (e X1)) := by first | exact superpose eq16 eq130 | exact mod_symm (superpose eq16 eq130) | exact superpose eq130 eq16 | exact mod_symm (superpose eq130 eq16)
  have eq134 (X0 X1 : G) : (w X0 X1) = (w (e X0) (e X1)) := by first | exact superpose eq20 eq132 | exact mod_symm (superpose eq20 eq132) | exact superpose eq132 eq20 | exact mod_symm (superpose eq132 eq20)
  have eq142 (X0 X1 X2 : G) : (w (X0 ◇ (e X1)) X2) = (w (e (X0 ◇ X1)) (e X2)) := by first | exact superpose eq30 eq134 | exact mod_symm (superpose eq30 eq134) | exact superpose eq134 eq30 | exact mod_symm (superpose eq134 eq30)
  have eq143 (X0 X1 X2 : G) : (w (e (X0 ◇ X1)) (e X2)) = (w ((e X0) ◇ X1) X2) := by first | exact superpose eq31 eq134 | exact mod_symm (superpose eq31 eq134) | exact superpose eq134 eq31 | exact mod_symm (superpose eq134 eq31)
  have eq144 (X0 X1 : G) : (w (e X0) (e X1)) = (w (e X0) X1) := by first | exact superpose eq16 eq134 | exact mod_symm (superpose eq16 eq134) | exact superpose eq134 eq16 | exact mod_symm (superpose eq134 eq16)
  have eq145 (X0 X1 : G) : (w (e X0) (e X1)) = (w (v (X0 ◇ X0)) X1) := by first | exact superpose eq29 eq134 | exact mod_symm (superpose eq29 eq134) | exact superpose eq134 eq29 | exact mod_symm (superpose eq134 eq29)
  have eq148 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w (e X2) (e (X0 ◇ X1))) := by first | exact superpose eq30 eq134 | exact mod_symm (superpose eq30 eq134) | exact superpose eq134 eq30 | exact mod_symm (superpose eq134 eq30)
  have eq149 (X0 X1 X2 : G) : (w (e X2) (e (X0 ◇ X1))) = (w X2 ((e X0) ◇ X1)) := by first | exact superpose eq31 eq134 | exact mod_symm (superpose eq31 eq134) | exact superpose eq134 eq31 | exact mod_symm (superpose eq134 eq31)
  have eq150 (X0 X1 : G) : (w X1 (e X0)) = (w (e X1) (e X0)) := by first | exact superpose eq16 eq134 | exact mod_symm (superpose eq16 eq134) | exact superpose eq134 eq16 | exact mod_symm (superpose eq134 eq16)
  have eq151 (X0 X1 : G) : (w (e X1) (e X0)) = (w X1 (v (X0 ◇ X0))) := by first | exact superpose eq29 eq134 | exact mod_symm (superpose eq29 eq134) | exact superpose eq134 eq29 | exact mod_symm (superpose eq134 eq29)
  have eq152 (X0 X1 X2 : G) : (w X2 (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = (w (e X2) (w X0 X1)) := by first | exact superpose eq20 eq134 | exact mod_symm (superpose eq20 eq134) | exact superpose eq134 eq20 | exact mod_symm (superpose eq134 eq20)
  have eq153 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq109 eq134 | exact mod_symm (superpose eq109 eq134) | exact superpose eq134 eq109 | exact mod_symm (superpose eq134 eq109)
  have eq155 (X0 X1 X2 : G) : (w X2 (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = (w X2 (w X0 X1)) := by first | exact superpose eq153 eq152 | exact mod_symm (superpose eq153 eq152) | exact superpose eq152 eq153 | exact mod_symm (superpose eq152 eq153)
  have eq156 (X0 X1 : G) : (w X1 (v (X0 ◇ X0))) = (w X1 X0) := by first | exact superpose eq134 eq151 | exact mod_symm (superpose eq134 eq151) | exact superpose eq151 eq134 | exact mod_symm (superpose eq151 eq134)
  have eq157 (X0 X1 : G) : (w X1 (e X0)) = (w X1 X0) := by first | exact superpose eq134 eq150 | exact mod_symm (superpose eq134 eq150) | exact superpose eq150 eq134 | exact mod_symm (superpose eq150 eq134)
  have eq158 (X0 X1 X2 : G) : (w X2 ((e X0) ◇ X1)) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq134 eq149 | exact mod_symm (superpose eq134 eq149) | exact superpose eq149 eq134 | exact mod_symm (superpose eq149 eq134)
  have eq159 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq134 eq148 | exact mod_symm (superpose eq134 eq148) | exact superpose eq148 eq134 | exact mod_symm (superpose eq148 eq134)
  have eq161 (X0 X1 : G) : (w X0 X1) = (w (v (X0 ◇ X0)) X1) := by first | exact superpose eq134 eq145 | exact mod_symm (superpose eq134 eq145) | exact superpose eq145 eq134 | exact mod_symm (superpose eq145 eq134)
  have eq162 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq134 eq144 | exact mod_symm (superpose eq134 eq144) | exact superpose eq144 eq134 | exact mod_symm (superpose eq144 eq134)
  have eq163 (X0 X1 X2 : G) : (w ((e X0) ◇ X1) X2) = (w (X0 ◇ X1) X2) := by first | exact superpose eq134 eq143 | exact mod_symm (superpose eq134 eq143) | exact superpose eq143 eq134 | exact mod_symm (superpose eq143 eq134)
  have eq164 (X0 X1 X2 : G) : (w (X0 ◇ (e X1)) X2) = (w (X0 ◇ X1) X2) := by first | exact superpose eq134 eq142 | exact mod_symm (superpose eq134 eq142) | exact superpose eq142 eq134 | exact mod_symm (superpose eq142 eq134)
  have eq176 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w (e X0) (v X1)) := by first | exact superpose eq19 eq125 | exact mod_symm (superpose eq19 eq125) | exact superpose eq125 eq19 | exact mod_symm (superpose eq125 eq19)
  have eq178 (X0 X1 : G) : (v (w X1 ((e X0) ◇ (e X0)))) = (w (v X1) (e X0)) := by first | exact superpose eq19 eq125 | exact mod_symm (superpose eq19 eq125) | exact superpose eq125 eq19 | exact mod_symm (superpose eq125 eq19)
  have eq180 (X0 X1 : G) : (v (w X1 ((e X0) ◇ (e X0)))) = (w (v X1) X0) := by first | exact superpose eq157 eq178 | exact mod_symm (superpose eq157 eq178) | exact superpose eq178 eq157 | exact mod_symm (superpose eq178 eq157)
  have eq182 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w X0 (v X1)) := by first | exact superpose eq162 eq176 | exact mod_symm (superpose eq162 eq176) | exact superpose eq176 eq162 | exact mod_symm (superpose eq176 eq162)
  have eq184 (X0 X1 : G) : (w (v X1) X0) = (v (w X1 (X0 ◇ (e X0)))) := by first | exact superpose eq158 eq180 | exact mod_symm (superpose eq158 eq180) | exact superpose eq180 eq158 | exact mod_symm (superpose eq180 eq158)
  have eq186 (X0 X1 : G) : (w X0 (v X1)) = (v (w (X0 ◇ (e X0)) X1)) := by first | exact superpose eq163 eq182 | exact mod_symm (superpose eq163 eq182) | exact superpose eq182 eq163 | exact mod_symm (superpose eq182 eq163)
  have eq188 (X0 X1 : G) : (w (v X1) X0) = (v (w X1 (X0 ◇ X0))) := by first | exact superpose eq159 eq184 | exact mod_symm (superpose eq159 eq184) | exact superpose eq184 eq159 | exact mod_symm (superpose eq184 eq159)
  have eq189 (X0 X1 : G) : (w X0 (v X1)) = (v (w (X0 ◇ X0) X1)) := by first | exact superpose eq164 eq186 | exact mod_symm (superpose eq164 eq186) | exact superpose eq186 eq164 | exact mod_symm (superpose eq186 eq164)
  have eq230 (X0 : G) : (e (v (v X0))) = (e (v (v (v (X0 ◇ X0))))) := by first | exact superpose eq15 eq39 | exact mod_symm (superpose eq15 eq39) | exact superpose eq39 eq15 | exact mod_symm (superpose eq39 eq15)
  have eq342 (X0 X1 : G) : ((v (e X0)) ◇ (e X1)) = (v (e (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq14 eq36 | exact mod_symm (superpose eq14 eq36) | exact superpose eq36 eq14 | exact mod_symm (superpose eq36 eq14)
  have eq350 (X0 X1 X2 : G) : (v (X2 ◇ (X0 ◇ (e (X1 ◇ X1))))) = ((v X2) ◇ ((v X0) ◇ (e X1))) := by first | exact superpose eq36 eq15 | exact mod_symm (superpose eq36 eq15) | exact superpose eq15 eq36 | exact mod_symm (superpose eq15 eq36)
  have eq367 (X0 X1 : G) : ((v (e X0)) ◇ (e X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq17 eq342 | exact mod_symm (superpose eq17 eq342) | exact superpose eq342 eq17 | exact mod_symm (superpose eq342 eq17)
  have eq382 (X0 X1 : G) : ((e (v X0)) ◇ (e X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq17 eq367 | exact mod_symm (superpose eq17 eq367) | exact superpose eq367 eq17 | exact mod_symm (superpose eq367 eq17)
  have eq389 (X0 X1 : G) : (e ((v X0) ◇ X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq14 eq382 | exact mod_symm (superpose eq14 eq382) | exact superpose eq382 eq14 | exact mod_symm (superpose eq382 eq14)
  have eq433 (X0 X1 X2 : G) : (v (X2 ◇ ((e (X0 ◇ X0)) ◇ X1))) = ((v X2) ◇ ((e X0) ◇ (v X1))) := by first | exact superpose eq37 eq15 | exact mod_symm (superpose eq37 eq15) | exact superpose eq15 eq37 | exact mod_symm (superpose eq15 eq37)
  have eq439 (X0 X1 X2 : G) : (v (w X2 ((e (X0 ◇ X0)) ◇ X1))) = (w (v X2) ((e X0) ◇ (v X1))) := by first | exact superpose eq37 eq125 | exact mod_symm (superpose eq37 eq125) | exact superpose eq125 eq37 | exact mod_symm (superpose eq125 eq37)
  have eq440 (X0 X1 X2 : G) : (v (w X2 ((e (X0 ◇ X0)) ◇ X1))) = (w (v X2) (X0 ◇ (v X1))) := by first | exact superpose eq158 eq439 | exact mod_symm (superpose eq158 eq439) | exact superpose eq439 eq158 | exact mod_symm (superpose eq439 eq158)
  have eq458 (X0 X1 X2 : G) : (w (v X2) (X0 ◇ (v X1))) = (v (w X2 ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq158 eq440 | exact mod_symm (superpose eq158 eq440) | exact superpose eq440 eq158 | exact mod_symm (superpose eq440 eq158)
  have eq833 (X0 X1 X2 : G) : (X2 ◇ (v (v X0))) = ((v (v X1)) ◇ ((v (v (X0 ◇ X1))) ◇ X2)) := by first | exact superpose eq15 eq74 | exact mod_symm (superpose eq15 eq74) | exact superpose eq74 eq15 | exact mod_symm (superpose eq74 eq15)
  have eq1156 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X1)) := by first | exact superpose eq76 eq13 | exact mod_symm (superpose eq76 eq13) | exact superpose eq13 eq76 | exact mod_symm (superpose eq13 eq76)
  have eq1247 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X2 ◇ X1) ◇ X3))) = (((X0 ◇ X1) ◇ X4) ◇ (X3 ◇ X2)) := by first | exact superpose eq76 eq77 | exact mod_symm (superpose eq76 eq77) | exact superpose eq77 eq76 | exact mod_symm (superpose eq77 eq76)
  have eq1257 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ (X4 ◇ X0)) ◇ X1)) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by first | exact superpose eq77 eq13 | exact mod_symm (superpose eq77 eq13) | exact superpose eq13 eq77 | exact mod_symm (superpose eq13 eq77)
  have eq1265 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq77 eq13 | exact mod_symm (superpose eq77 eq13) | exact superpose eq13 eq77 | exact mod_symm (superpose eq13 eq77)
  have eq2172 (X0 X1 : G) : (v (e (v (X0 ◇ X1)))) = (e (v (v ((e X0) ◇ X1)))) := by first | exact superpose eq94 eq17 | exact mod_symm (superpose eq94 eq17) | exact superpose eq17 eq94 | exact mod_symm (superpose eq17 eq94)
  have eq2199 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (e (v (v ((e X0) ◇ X1)))) := by first | exact superpose eq17 eq2172 | exact mod_symm (superpose eq17 eq2172) | exact superpose eq2172 eq17 | exact mod_symm (superpose eq2172 eq17)
  have eq2451 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ (e (X0 ◇ X1)))) = (w X2 (X3 ◇ ((e X0) ◇ X1))) := by first | exact superpose eq31 eq159 | exact mod_symm (superpose eq31 eq159) | exact superpose eq159 eq31 | exact mod_symm (superpose eq159 eq31)
  have eq2518 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((e X0) ◇ X1))) = (w X2 (X3 ◇ (X0 ◇ X1))) := by first | exact superpose eq159 eq2451 | exact mod_symm (superpose eq159 eq2451) | exact superpose eq2451 eq159 | exact mod_symm (superpose eq2451 eq159)
  have eq3328 (X0 X1 X2 X3 X4 : G) : (w X3 (X4 ◇ (X0 ◇ (X1 ◇ (e X2))))) = (w X3 (X4 ◇ (e (X0 ◇ (X1 ◇ X2))))) := by first | exact superpose eq68 eq159 | exact mod_symm (superpose eq68 eq159) | exact superpose eq159 eq68 | exact mod_symm (superpose eq159 eq68)
  have eq3339 (X0 X1 X2 X3 X4 : G) : (w X3 (X4 ◇ (X0 ◇ (X1 ◇ (e X2))))) = (w X3 (X4 ◇ (X0 ◇ (X1 ◇ X2)))) := by first | exact superpose eq159 eq3328 | exact mod_symm (superpose eq159 eq3328) | exact superpose eq3328 eq159 | exact mod_symm (superpose eq3328 eq159)
  have eq4455 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X4)) = (X2 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4)) := by first | exact superpose eq13 eq1156 | exact mod_symm (superpose eq13 eq1156) | exact superpose eq1156 eq13 | exact mod_symm (superpose eq1156 eq13)
  have eq4471 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by first | exact superpose eq1156 eq76 | exact mod_symm (superpose eq1156 eq76) | exact superpose eq76 eq1156 | exact mod_symm (superpose eq76 eq1156)
  have eq4473 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ ((X0 ◇ X3) ◇ X1))) = (((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ X3) := by first | exact superpose eq1156 eq77 | exact mod_symm (superpose eq1156 eq77) | exact superpose eq77 eq1156 | exact mod_symm (superpose eq77 eq1156)
  have eq4498 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (((X1 ◇ X4) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq1156 eq76 | exact mod_symm (superpose eq1156 eq76) | exact superpose eq76 eq1156 | exact mod_symm (superpose eq76 eq1156)
  have eq4507 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X4) ◇ X0))) := by first | exact superpose eq1247 eq4498 | exact mod_symm (superpose eq1247 eq4498) | exact superpose eq4498 eq1247 | exact mod_symm (superpose eq4498 eq1247)
  have eq4528 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X4)) = (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X4) ◇ X2)))) := by first | exact superpose eq4473 eq4455 | exact mod_symm (superpose eq4473 eq4455) | exact superpose eq4455 eq4473 | exact mod_symm (superpose eq4455 eq4473)
  have eq4539 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ (X0 ◇ X3)))) := by first | exact superpose eq4471 eq4507 | exact mod_symm (superpose eq4471 eq4507) | exact superpose eq4507 eq4471 | exact mod_symm (superpose eq4507 eq4471)
  have eq4546 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ (X0 ◇ (X1 ◇ (X4 ◇ ((X3 ◇ X2) ◇ X0))))) := by first | exact superpose eq1247 eq4539 | exact mod_symm (superpose eq1247 eq4539) | exact superpose eq4539 eq1247 | exact mod_symm (superpose eq4539 eq1247)
  have eq4549 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X4) = (X1 ◇ ((X4 ◇ X3) ◇ (X1 ◇ X2))) := by first | exact superpose eq4528 eq4546 | exact mod_symm (superpose eq4528 eq4546) | exact superpose eq4546 eq4528 | exact mod_symm (superpose eq4546 eq4528)
  have eq4587 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ ((v X0) ◇ X2)) := by first | exact superpose eq15 eq4471 | exact mod_symm (superpose eq15 eq4471) | exact superpose eq4471 eq15 | exact mod_symm (superpose eq4471 eq15)
  have eq4692 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := by first | exact superpose eq4471 eq13 | exact mod_symm (superpose eq4471 eq13) | exact superpose eq13 eq4471 | exact mod_symm (superpose eq13 eq4471)
  have eq4735 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by first | exact superpose eq4471 eq13 | exact mod_symm (superpose eq4471 eq13) | exact superpose eq13 eq4471 | exact mod_symm (superpose eq13 eq4471)
  have eq4766 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by first | exact superpose eq4471 eq13 | exact mod_symm (superpose eq4471 eq13) | exact superpose eq13 eq4471 | exact mod_symm (superpose eq13 eq4471)
  have eq4789 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0))) := by first | exact superpose eq1257 eq4735 | exact mod_symm (superpose eq1257 eq4735) | exact superpose eq4735 eq1257 | exact mod_symm (superpose eq4735 eq1257)
  have eq4884 (X0 X2 X3 : G) : (X3 ◇ X2) = (((X3 ◇ X0) ◇ X0) ◇ X2) := by first | exact superpose eq4549 eq4789 | exact mod_symm (superpose eq4549 eq4789) | exact superpose eq4789 eq4549 | exact mod_symm (superpose eq4789 eq4549)
  have eq5158 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X2) := by first | exact superpose eq4692 eq76 | exact mod_symm (superpose eq4692 eq76) | exact superpose eq76 eq4692 | exact mod_symm (superpose eq76 eq4692)
  have eq5159 (X0 X1 : G) : (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = (w X0 ((X1 ◇ X0) ◇ X0)) := by first | exact superpose eq4692 eq106 | exact mod_symm (superpose eq4692 eq106) | exact superpose eq106 eq4692 | exact mod_symm (superpose eq106 eq4692)
  have eq5169 (X0 X1 X2 : G) : (w ((X0 ◇ X1) ◇ X1) X2) = (w (v (((X0 ◇ X1) ◇ X1) ◇ X0)) X2) := by first | exact superpose eq4692 eq161 | exact mod_symm (superpose eq4692 eq161) | exact superpose eq161 eq4692 | exact mod_symm (superpose eq161 eq4692)
  have eq5213 (X0 X1 X2 : G) : (w X0 ((X1 ◇ X2) ◇ X2)) = (e (v (v (v ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X1))))) := by first | exact superpose eq4692 eq20 | exact mod_symm (superpose eq4692 eq20) | exact superpose eq20 eq4692 | exact mod_symm (superpose eq20 eq4692)
  have eq5260 (X0 X1 X2 : G) : (e (v (v (v ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = (w X0 ((X1 ◇ X2) ◇ X2)) := by first | exact superpose eq4692 eq5213 | exact mod_symm (superpose eq4692 eq5213) | exact superpose eq5213 eq4692 | exact mod_symm (superpose eq5213 eq4692)
  have eq5303 (X0 X1 X2 : G) : (w ((X0 ◇ X1) ◇ X1) X2) = (w (v (X0 ◇ X0)) X2) := by first | exact superpose eq4884 eq5169 | exact mod_symm (superpose eq4884 eq5169) | exact superpose eq5169 eq4884 | exact mod_symm (superpose eq5169 eq4884)
  have eq5312 (X0 X1 : G) : (w X0 X1) = (w X0 ((X1 ◇ X0) ◇ X0)) := by first | exact superpose eq20 eq5159 | exact mod_symm (superpose eq20 eq5159) | exact superpose eq5159 eq20 | exact mod_symm (superpose eq5159 eq20)
  have eq5341 (X0 X1 X2 : G) : (w X0 X1) = (w X0 ((X1 ◇ X2) ◇ X2)) := by first | exact superpose eq20 eq5260 | exact mod_symm (superpose eq20 eq5260) | exact superpose eq5260 eq20 | exact mod_symm (superpose eq5260 eq20)
  have eq5369 (X0 X1 X2 : G) : (w ((X0 ◇ X1) ◇ X1) X2) = (w X0 X2) := by first | exact superpose eq161 eq5303 | exact mod_symm (superpose eq161 eq5303) | exact superpose eq5303 eq161 | exact mod_symm (superpose eq5303 eq161)
  have eq5855 (X0 X1 X2 : G) : (w X2 (X2 ◇ X1)) = (e (v (v (v ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X1)))))) := by first | exact superpose eq1265 eq20 | exact mod_symm (superpose eq1265 eq20) | exact superpose eq20 eq1265 | exact mod_symm (superpose eq20 eq1265)
  have eq5867 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (v (X2 ◇ X3))))) = (((v X3) ◇ X1) ◇ (v X2)) := by first | exact superpose eq1265 eq74 | exact mod_symm (superpose eq1265 eq74) | exact superpose eq74 eq1265 | exact mod_symm (superpose eq74 eq1265)
  have eq5899 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X5) = (((X4 ◇ X5) ◇ X3) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by first | exact superpose eq1265 eq76 | exact mod_symm (superpose eq1265 eq76) | exact superpose eq76 eq1265 | exact mod_symm (superpose eq76 eq1265)
  have eq5913 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X5) = (X4 ◇ (X3 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X5) ◇ X0))) := by first | exact superpose eq1247 eq5899 | exact mod_symm (superpose eq1247 eq5899) | exact superpose eq5899 eq1247 | exact mod_symm (superpose eq5899 eq1247)
  have eq5943 (X0 X1 X2 : G) : (w X2 (X2 ◇ X1)) = (e (v (v (v (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))))))) := by first | exact superpose eq4471 eq5855 | exact mod_symm (superpose eq4471 eq5855) | exact superpose eq5855 eq4471 | exact mod_symm (superpose eq5855 eq4471)
  have eq6035 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X5) = (X4 ◇ (X3 ◇ (X2 ◇ (X5 ◇ X1)))) := by first | exact superpose eq77 eq5913 | exact mod_symm (superpose eq77 eq5913) | exact superpose eq5913 eq77 | exact mod_symm (superpose eq5913 eq77)
  have eq6047 (X0 X1 X2 : G) : (w X2 (X2 ◇ X1)) = (e (v (v (v (X1 ◇ ((X1 ◇ X0) ◇ X0)))))) := by first | exact superpose eq4766 eq5943 | exact mod_symm (superpose eq4766 eq5943) | exact superpose eq5943 eq4766 | exact mod_symm (superpose eq5943 eq4766)
  have eq6090 (X1 X2 : G) : (w X2 (X2 ◇ X1)) = (e (v (v (v (X1 ◇ X1))))) := by first | exact superpose eq4692 eq6047 | exact mod_symm (superpose eq4692 eq6047) | exact superpose eq6047 eq4692 | exact mod_symm (superpose eq6047 eq4692)
  have eq6116 (X1 X2 : G) : (e (v (v X1))) = (w X2 (X2 ◇ X1)) := by first | exact superpose eq230 eq6090 | exact mod_symm (superpose eq230 eq6090) | exact superpose eq6090 eq230 | exact mod_symm (superpose eq6090 eq230)
  have eq6157 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (e (v (v (X2 ◇ (X3 ◇ X1))))) := by first | exact superpose eq1265 eq6116 | exact mod_symm (superpose eq1265 eq6116) | exact superpose eq6116 eq1265 | exact mod_symm (superpose eq6116 eq1265)
  have eq6162 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (w (e (v X1)) (X0 ◇ (e (v X1)))) := by first | exact superpose eq78 eq6116 | exact mod_symm (superpose eq78 eq6116) | exact superpose eq6116 eq78 | exact mod_symm (superpose eq6116 eq78)
  have eq6171 (X0 X1 X2 : G) : (w (v X2) (X0 ◇ (v X1))) = (e (v (v ((v (X1 ◇ X2)) ◇ X0)))) := by first | exact superpose eq74 eq6116 | exact mod_symm (superpose eq74 eq6116) | exact superpose eq6116 eq74 | exact mod_symm (superpose eq6116 eq74)
  have eq6238 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (w (v X1) (X0 ◇ (e (v X1)))) := by first | exact superpose eq162 eq6162 | exact mod_symm (superpose eq162 eq6162) | exact superpose eq6162 eq162 | exact mod_symm (superpose eq6162 eq162)
  have eq6253 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (w (v X1) (X0 ◇ (v X1))) := by first | exact superpose eq159 eq6238 | exact mod_symm (superpose eq159 eq6238) | exact superpose eq6238 eq159 | exact mod_symm (superpose eq6238 eq159)
  have eq6264 (X0 X1 : G) : (e (v (v (X1 ◇ X0)))) = (w (v X1) (X0 ◇ (v X1))) := by first | exact superpose eq2199 eq6253 | exact mod_symm (superpose eq2199 eq6253) | exact superpose eq6253 eq2199 | exact mod_symm (superpose eq6253 eq2199)
  have eq10452 (X0 X1 : G) : (e ((v (v (v X1))) ◇ (v (v (X0 ◇ X1))))) = (e (v ((v (v (X0 ◇ X1))) ◇ (v (v X0))))) := by first | exact superpose eq833 eq389 | exact mod_symm (superpose eq833 eq389) | exact superpose eq389 eq833 | exact mod_symm (superpose eq389 eq833)
  have eq10510 (X0 X1 : G) : (e ((v (v (v X1))) ◇ (v (v (X0 ◇ X1))))) = (e (v (v ((v (X0 ◇ X1)) ◇ (v X0))))) := by first | exact superpose eq15 eq10452 | exact mod_symm (superpose eq15 eq10452) | exact superpose eq10452 eq15 | exact mod_symm (superpose eq10452 eq15)
  have eq10593 (X0 X1 : G) : (e ((v (v (v X1))) ◇ (v (v (X0 ◇ X1))))) = (w (v X1) ((v X0) ◇ (v X0))) := by first | exact superpose eq6171 eq10510 | exact mod_symm (superpose eq6171 eq10510) | exact superpose eq10510 eq6171 | exact mod_symm (superpose eq10510 eq6171)
  have eq10661 (X0 X1 : G) : (w (v X1) (v (X0 ◇ X0))) = (e ((v (v (v X1))) ◇ (v (v (X0 ◇ X1))))) := by first | exact superpose eq15 eq10593 | exact mod_symm (superpose eq15 eq10593) | exact superpose eq10593 eq15 | exact mod_symm (superpose eq10593 eq15)
  have eq10701 (X0 X1 : G) : (w (v X1) (v (X0 ◇ X0))) = (e (v ((v (v X1)) ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq15 eq10661 | exact mod_symm (superpose eq15 eq10661) | exact superpose eq10661 eq15 | exact mod_symm (superpose eq10661 eq15)
  have eq10727 (X0 X1 : G) : (w (v X1) (v (X0 ◇ X0))) = (e (v (v ((v X1) ◇ (X0 ◇ X1))))) := by first | exact superpose eq15 eq10701 | exact mod_symm (superpose eq15 eq10701) | exact superpose eq10701 eq15 | exact mod_symm (superpose eq10701 eq15)
  have eq10743 (X0 X1 : G) : (w (v X1) (v (X0 ◇ X0))) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq4471 eq10727 | exact mod_symm (superpose eq4471 eq10727) | exact superpose eq10727 eq4471 | exact mod_symm (superpose eq10727 eq4471)
  have eq10753 (X0 X1 : G) : (v (w X1 (X0 ◇ X0))) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq125 eq10743 | exact mod_symm (superpose eq125 eq10743) | exact superpose eq10743 eq125 | exact mod_symm (superpose eq10743 eq125)
  have eq10759 (X0 X1 : G) : (w (v X1) X0) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq188 eq10753 | exact mod_symm (superpose eq188 eq10753) | exact superpose eq10753 eq188 | exact mod_symm (superpose eq10753 eq188)
  have eq11110 (X0 X1 X2 : G) : (v (X0 ◇ X1)) = (((v (X0 ◇ X1)) ◇ X2) ◇ X2) := by first | exact superpose eq15 eq5158 | exact mod_symm (superpose eq15 eq5158) | exact superpose eq5158 eq15 | exact mod_symm (superpose eq5158 eq15)
  have eq11298 (X0 X1 X2 : G) : (w X2 (w X1 X0)) = (w X2 (v (v (v ((X0 ◇ (X1 ◇ X1)) ◇ X0))))) := by first | exact superpose eq4471 eq155 | exact mod_symm (superpose eq4471 eq155) | exact superpose eq155 eq4471 | exact mod_symm (superpose eq155 eq4471)
  have eq11301 (X0 X1 X2 X3 : G) : (w X3 (w ((X0 ◇ X1) ◇ X1) X2)) = (w X3 (v (v (v ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X2))))) := by first | exact superpose eq4884 eq155 | exact mod_symm (superpose eq4884 eq155) | exact superpose eq155 eq4884 | exact mod_symm (superpose eq155 eq4884)
  have eq11394 (X0 X1 X2 X3 : G) : (w X3 (w ((X0 ◇ X1) ◇ X1) X2)) = (w X3 (v (v (v (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))))))) := by first | exact superpose eq6035 eq11301 | exact mod_symm (superpose eq6035 eq11301) | exact superpose eq11301 eq6035 | exact mod_symm (superpose eq11301 eq6035)
  have eq11438 (X0 X1 X2 X3 : G) : (w X3 (w ((X0 ◇ X1) ◇ X1) X2)) = (w X3 (v (v (v ((X0 ◇ (X2 ◇ X2)) ◇ X0))))) := by first | exact superpose eq13 eq11394 | exact mod_symm (superpose eq13 eq11394) | exact superpose eq11394 eq13 | exact mod_symm (superpose eq11394 eq13)
  have eq11473 (X0 X1 X2 X3 : G) : (w X3 (w ((X0 ◇ X1) ◇ X1) X2)) = (w X3 (w X2 X0)) := by first | exact superpose eq11298 eq11438 | exact mod_symm (superpose eq11298 eq11438) | exact superpose eq11438 eq11298 | exact mod_symm (superpose eq11438 eq11298)
  have eq11498 (X0 X2 X3 : G) : (w X3 (w X2 X0)) = (w X3 (w X0 X2)) := by first | exact superpose eq5369 eq11473 | exact mod_symm (superpose eq5369 eq11473) | exact superpose eq11473 eq5369 | exact mod_symm (superpose eq11473 eq5369)
  have eq11577 (X0 : G) : (v (w X0 X0)) = (w (v X0) (X0 ◇ (v X0))) := by first | exact superpose eq5312 eq458 | exact mod_symm (superpose eq5312 eq458) | exact superpose eq458 eq5312 | exact mod_symm (superpose eq458 eq5312)
  have eq11617 (X0 : G) : (e (v (v (X0 ◇ X0)))) = (v (w X0 X0)) := by first | exact superpose eq6264 eq11577 | exact mod_symm (superpose eq6264 eq11577) | exact superpose eq11577 eq6264 | exact mod_symm (superpose eq11577 eq6264)
  have eq11664 (X0 : G) : (e (v X0)) = (v (w X0 X0)) := by first | exact superpose eq39 eq11617 | exact mod_symm (superpose eq39 eq11617) | exact superpose eq11617 eq39 | exact mod_symm (superpose eq11617 eq39)
  have eq12075 (X0 : G) : (e (v (X0 ◇ X0))) = (w X0 (v (X0 ◇ X0))) := by first | exact superpose eq11664 eq189 | exact mod_symm (superpose eq11664 eq189) | exact superpose eq189 eq11664 | exact mod_symm (superpose eq189 eq11664)
  have eq12135 (X0 : G) : (w X0 X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq156 eq12075 | exact mod_symm (superpose eq156 eq12075) | exact superpose eq12075 eq156 | exact mod_symm (superpose eq12075 eq156)
  have eq12190 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq29 eq12135 | exact mod_symm (superpose eq29 eq12135) | exact superpose eq12135 eq29 | exact mod_symm (superpose eq12135 eq29)
  have eq12727 : (w x y) ≠ (w y (w (e x) x)) := by first | exact superpose eq12190 eq21 | exact mod_symm (superpose eq12190 eq21) | exact superpose eq21 eq12190 | exact mod_symm (superpose eq21 eq12190)
  have eq12728 : (w x y) ≠ (w y (w x (e x))) := by first | exact superpose eq11498 eq12727 | exact mod_symm (superpose eq11498 eq12727) | exact superpose eq12727 eq11498 | exact mod_symm (superpose eq12727 eq11498)
  have eq12779 : (w x y) ≠ (w y (w x x)) := by first | exact superpose eq157 eq12728 | exact mod_symm (superpose eq157 eq12728) | exact superpose eq12728 eq157 | exact mod_symm (superpose eq12728 eq157)
  have eq12820 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq12190 eq12779 | exact mod_symm (superpose eq12190 eq12779) | exact superpose eq12779 eq12190 | exact mod_symm (superpose eq12779 eq12190)
  have eq12843 : (w x y) ≠ (w y x) := by first | exact superpose eq157 eq12820 | exact mod_symm (superpose eq157 eq12820) | exact superpose eq12820 eq157 | exact mod_symm (superpose eq12820 eq157)
  have eq12882 (X0 X1 X2 X3 X4 : G) : (v (X0 ◇ (X1 ◇ X2))) = ((v ((X2 ◇ ((X3 ◇ (e (X4 ◇ X4))) ◇ X0)) ◇ X1)) ◇ ((v X3) ◇ (e X4))) := by first | exact superpose eq77 eq350 | exact mod_symm (superpose eq77 eq350) | exact superpose eq350 eq77 | exact mod_symm (superpose eq350 eq77)
  have eq13021 (X0 X1 X2 X3 X4 : G) : (v (X0 ◇ (X1 ◇ X2))) = ((e X4) ◇ (v (X3 ◇ ((X2 ◇ ((X3 ◇ (e (X4 ◇ X4))) ◇ X0)) ◇ X1)))) := by first | exact superpose eq4587 eq12882 | exact mod_symm (superpose eq4587 eq12882) | exact superpose eq12882 eq4587 | exact mod_symm (superpose eq12882 eq4587)
  have eq13119 (X0 X1 X2 X3 X4 : G) : (v (X0 ◇ (X1 ◇ X2))) = ((e X4) ◇ (v (X3 ◇ ((e (X4 ◇ X4)) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0))))))) := by first | exact superpose eq6035 eq13021 | exact mod_symm (superpose eq6035 eq13021) | exact superpose eq13021 eq6035 | exact mod_symm (superpose eq13021 eq6035)
  have eq13207 (X0 X1 X2 X3 X4 : G) : (v (X0 ◇ (X1 ◇ X2))) = ((e X4) ◇ ((v X3) ◇ ((e X4) ◇ (v (X3 ◇ (X2 ◇ (X1 ◇ X0))))))) := by first | exact superpose eq433 eq13119 | exact mod_symm (superpose eq433 eq13119) | exact superpose eq13119 eq433 | exact mod_symm (superpose eq13119 eq433)
  have eq13275 (X0 X1 X2 X3 : G) : (v (X0 ◇ (X1 ◇ X2))) = (((v (X2 ◇ (X1 ◇ X0))) ◇ (v X3)) ◇ (v X3)) := by first | exact superpose eq5867 eq13207 | exact mod_symm (superpose eq5867 eq13207) | exact superpose eq13207 eq5867 | exact mod_symm (superpose eq13207 eq5867)
  have eq13328 (X0 X1 X2 : G) : (v (X0 ◇ (X1 ◇ X2))) = (v (X2 ◇ (X1 ◇ X0))) := by first | exact superpose eq11110 eq13275 | exact mod_symm (superpose eq11110 eq13275) | exact superpose eq13275 eq11110 | exact mod_symm (superpose eq13275 eq11110)
  have eq13917 (X0 X1 X2 : G) : (w X2 (e (v X1))) = (w X2 ((X0 ◇ (e (v X1))) ◇ ((e X1) ◇ X0))) := by first | exact superpose eq78 eq5341 | exact mod_symm (superpose eq78 eq5341) | exact superpose eq5341 eq78 | exact mod_symm (superpose eq5341 eq78)
  have eq13936 (X0 X1 X2 X3 : G) : (w X3 (X0 ◇ (X1 ◇ X2))) = (w X3 (X2 ◇ (X1 ◇ X0))) := by first | exact superpose eq77 eq5341 | exact mod_symm (superpose eq77 eq5341) | exact superpose eq5341 eq77 | exact mod_symm (superpose eq5341 eq77)
  have eq14044 (X0 X1 X2 : G) : (w X2 (e (v X1))) = (w X2 ((X0 ◇ (e (v X1))) ◇ (X1 ◇ X0))) := by first | exact superpose eq2518 eq13917 | exact mod_symm (superpose eq2518 eq13917) | exact superpose eq13917 eq2518 | exact mod_symm (superpose eq13917 eq2518)
  have eq14077 (X0 X1 X2 : G) : (w X2 (e (v X1))) = (w X2 (X0 ◇ (X1 ◇ (X0 ◇ (e (v X1)))))) := by first | exact superpose eq13936 eq14044 | exact mod_symm (superpose eq13936 eq14044) | exact superpose eq14044 eq13936 | exact mod_symm (superpose eq14044 eq13936)
  have eq14100 (X0 X1 X2 : G) : (w X2 (e (v X1))) = (w X2 (X0 ◇ (X1 ◇ (X0 ◇ (v X1))))) := by first | exact superpose eq3339 eq14077 | exact mod_symm (superpose eq3339 eq14077) | exact superpose eq14077 eq3339 | exact mod_symm (superpose eq14077 eq3339)
  have eq14111 (X1 X2 : G) : (w X2 (e (v X1))) = (e (v (v ((v X1) ◇ (X2 ◇ X1))))) := by first | exact superpose eq6157 eq14100 | exact mod_symm (superpose eq6157 eq14100) | exact superpose eq14100 eq6157 | exact mod_symm (superpose eq14100 eq6157)
  have eq14117 (X1 X2 : G) : (w X2 (e (v X1))) = (e (v (v (X1 ◇ (X2 ◇ (v X1)))))) := by first | exact superpose eq13328 eq14111 | exact mod_symm (superpose eq13328 eq14111) | exact superpose eq14111 eq13328 | exact mod_symm (superpose eq14111 eq13328)
  have eq14119 (X1 X2 : G) : (w (v X1) X2) = (w X2 (e (v X1))) := by first | exact superpose eq10759 eq14117 | exact mod_symm (superpose eq10759 eq14117) | exact superpose eq14117 eq10759 | exact mod_symm (superpose eq14117 eq10759)
  have eq14121 (X1 X2 : G) : (w (v X1) X2) = (w X2 (v X1)) := by first | exact superpose eq157 eq14119 | exact mod_symm (superpose eq157 eq14119) | exact superpose eq14119 eq157 | exact mod_symm (superpose eq14119 eq157)
  have eq14655 (X0 X1 : G) : (w (e X0) X1) = (w X1 (e X0)) := by first | exact superpose eq19 eq14121 | exact mod_symm (superpose eq19 eq14121) | exact superpose eq14121 eq19 | exact mod_symm (superpose eq14121 eq19)
  have eq14769 (X0 X1 : G) : (w (e X0) X1) = (w X1 X0) := by first | exact superpose eq157 eq14655 | exact mod_symm (superpose eq157 eq14655) | exact superpose eq14655 eq157 | exact mod_symm (superpose eq14655 eq157)
  have eq15222 (X0 X1 : G) : (w X0 X1) = (w X1 X0) := by first | exact superpose eq14769 eq162 | exact mod_symm (superpose eq14769 eq162) | exact superpose eq162 eq14769 | exact mod_symm (superpose eq162 eq14769)
  have eq15943 : (w x y) ≠ (w x y) := by first | exact superpose eq15222 eq12843 | exact mod_symm (superpose eq15222 eq12843) | exact superpose eq12843 eq15222 | exact mod_symm (superpose eq12843 eq15222)
  first | exact eq15943 rfl | exact eq15943 _ rfl | exact eq15943 _ _ rfl | exact eq15943 _ _ _ rfl


/-- Equation 3675 `x ◇ x = (y ◇ x) ◇ (x ◇ y)` is term-definable from equation 3607 over finite magmas, via the term
`x □ y := u^[2N+1] (x ◇ y)` with `u a = (a ◇ a)`. -/
private theorem aux3607_3675 [Magma G] (h : Equation3607 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a)
    (hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a)
    (hw : ∀ a b : G, w a b = (e (v ((a ◇ b)))))
    (x y : G) :
    (w x x) =
      (w (w y x) (w x y)) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ X1))) := mod_symm (hw ..)
  have eq21 : (w x x) ≠ (w (w y x) (w x y)) := mod_symm nh
  have eq28 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq29 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq31 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq32 (X0 X1 X2 : G) : (e ((v (X0 ◇ X1)) ◇ X2)) = ((w X0 X1) ◇ (e X2)) := by first | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14) | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20)
  have eq33 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq34 (X0 X1 X2 : G) : (e (X2 ◇ (v (X0 ◇ X1)))) = ((e X2) ◇ (w X0 X1)) := by first | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14) | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20)
  have eq35 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq36 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (e (X0 ◇ X1)))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq37 (X0 X1 : G) : (e (e (v (X0 ◇ X1)))) = (w (e X0) (e X1)) := by first | exact superpose eq17 eq36 | exact mod_symm (superpose eq17 eq36) | exact superpose eq36 eq17 | exact mod_symm (superpose eq36 eq17)
  have eq38 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq35 | exact mod_symm (superpose eq17 eq35) | exact superpose eq35 eq17 | exact mod_symm (superpose eq35 eq17)
  have eq39 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq40 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq31 | exact mod_symm (superpose eq14 eq31) | exact superpose eq31 eq14 | exact mod_symm (superpose eq31 eq14)
  have eq41 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq16 eq37 | exact mod_symm (superpose eq16 eq37) | exact superpose eq37 eq16 | exact mod_symm (superpose eq37 eq16)
  have eq42 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq20 eq38 | exact mod_symm (superpose eq20 eq38) | exact superpose eq38 eq20 | exact mod_symm (superpose eq38 eq20)
  have eq43 (X0 X1 : G) : (w X0 X1) = (w (e X0) (e X1)) := by first | exact superpose eq20 eq41 | exact mod_symm (superpose eq20 eq41) | exact superpose eq41 eq20 | exact mod_symm (superpose eq41 eq20)
  have eq45 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq47 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq48 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (w (v X0) (v X1)) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq49 (X0 X1 : G) : (v (w X0 X1)) = (w (v X0) (v X1)) := by first | exact superpose eq28 eq48 | exact mod_symm (superpose eq28 eq48) | exact superpose eq48 eq28 | exact mod_symm (superpose eq48 eq28)
  have eq50 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq47 | exact mod_symm (superpose eq14 eq47) | exact superpose eq47 eq14 | exact mod_symm (superpose eq47 eq14)
  have eq51 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq45 | exact mod_symm (superpose eq14 eq45) | exact superpose eq45 eq14 | exact mod_symm (superpose eq45 eq14)
  have eq53 (X0 X1 X2 : G) : ((e X2) ◇ (w X0 X1)) = (e (X2 ◇ (w X0 X1))) := by first | exact superpose eq29 eq14 | exact mod_symm (superpose eq29 eq14) | exact superpose eq14 eq29 | exact mod_symm (superpose eq14 eq29)
  have eq54 (X0 X1 X2 : G) : ((w X0 X1) ◇ (e X2)) = (e ((w X0 X1) ◇ X2)) := by first | exact superpose eq29 eq14 | exact mod_symm (superpose eq29 eq14) | exact superpose eq14 eq29 | exact mod_symm (superpose eq14 eq29)
  have eq80 (X0 X1 : G) : (X1 ◇ (v (e X0))) = ((v (e X0)) ◇ ((e X0) ◇ X1)) := by first | exact superpose eq18 eq13 | exact mod_symm (superpose eq18 eq13) | exact superpose eq13 eq18 | exact mod_symm (superpose eq13 eq18)
  have eq81 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq82 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ X1)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq83 (X0 X1 X2 : G) : (e (v (X0 ◇ X1))) = (w X2 ((X1 ◇ X2) ◇ X0)) := by first | exact superpose eq13 eq20 | exact mod_symm (superpose eq13 eq20) | exact superpose eq20 eq13 | exact mod_symm (superpose eq20 eq13)
  have eq84 (X0 X1 X2 : G) : (w X0 X1) = (w X2 ((X1 ◇ X2) ◇ X0)) := by first | exact superpose eq20 eq83 | exact mod_symm (superpose eq20 eq83) | exact superpose eq83 eq20 | exact mod_symm (superpose eq83 eq20)
  have eq85 (X0 X1 : G) : (X1 ◇ (e (v X0))) = ((e (v X0)) ◇ ((e X0) ◇ X1)) := by first | exact superpose eq17 eq80 | exact mod_symm (superpose eq17 eq80) | exact superpose eq80 eq17 | exact mod_symm (superpose eq80 eq17)
  have eq86 (X0 X1 : G) : (w (e X0) (e X1)) = (w (e X0) X1) := by first | exact superpose eq16 eq43 | exact mod_symm (superpose eq16 eq43) | exact superpose eq43 eq16 | exact mod_symm (superpose eq43 eq16)
  have eq87 (X0 X1 X2 : G) : (w (v (X0 ◇ X1)) X2) = (w (w X0 X1) (e X2)) := by first | exact superpose eq20 eq43 | exact mod_symm (superpose eq20 eq43) | exact superpose eq43 eq20 | exact mod_symm (superpose eq43 eq20)
  have eq88 (X0 X1 X2 : G) : (w (w X0 X1) (e X2)) = (w (w X0 X1) X2) := by first | exact superpose eq29 eq43 | exact mod_symm (superpose eq29 eq43) | exact superpose eq43 eq29 | exact mod_symm (superpose eq43 eq29)
  have eq89 (X0 X1 : G) : (w X1 (e X0)) = (w (e X1) (e X0)) := by first | exact superpose eq16 eq43 | exact mod_symm (superpose eq16 eq43) | exact superpose eq43 eq16 | exact mod_symm (superpose eq43 eq16)
  have eq90 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w (e X2) (w X0 X1)) := by first | exact superpose eq20 eq43 | exact mod_symm (superpose eq20 eq43) | exact superpose eq43 eq20 | exact mod_symm (superpose eq43 eq20)
  have eq91 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq29 eq43 | exact mod_symm (superpose eq29 eq43) | exact superpose eq43 eq29 | exact mod_symm (superpose eq43 eq29)
  have eq99 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w X2 (w X0 X1)) := by first | exact superpose eq91 eq90 | exact mod_symm (superpose eq91 eq90) | exact superpose eq90 eq91 | exact mod_symm (superpose eq90 eq91)
  have eq100 (X0 X1 : G) : (w X1 X0) = (w X1 (e X0)) := by first | exact superpose eq43 eq89 | exact mod_symm (superpose eq43 eq89) | exact superpose eq89 eq43 | exact mod_symm (superpose eq89 eq43)
  have eq101 (X0 X1 X2 : G) : (w (v (X0 ◇ X1)) X2) = (w (w X0 X1) X2) := by first | exact superpose eq88 eq87 | exact mod_symm (superpose eq88 eq87) | exact superpose eq87 eq88 | exact mod_symm (superpose eq87 eq88)
  have eq102 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq43 eq86 | exact mod_symm (superpose eq43 eq86) | exact superpose eq86 eq43 | exact mod_symm (superpose eq86 eq43)
  have eq106 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = ((e (X0 ◇ X1)) ◇ (e X2)) := by first | exact superpose eq39 eq14 | exact mod_symm (superpose eq39 eq14) | exact superpose eq14 eq39 | exact mod_symm (superpose eq14 eq39)
  have eq114 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w (e X2) (e (X0 ◇ X1))) := by first | exact superpose eq39 eq43 | exact mod_symm (superpose eq39 eq43) | exact superpose eq43 eq39 | exact mod_symm (superpose eq43 eq39)
  have eq115 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq43 eq114 | exact mod_symm (superpose eq43 eq114) | exact superpose eq114 eq43 | exact mod_symm (superpose eq114 eq43)
  have eq119 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = (e ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq14 eq106 | exact mod_symm (superpose eq14 eq106) | exact superpose eq106 eq14 | exact mod_symm (superpose eq106 eq14)
  have eq275 (X0 X1 X2 X3 : G) : (w X2 X3) = (w ((X1 ◇ X3) ◇ X0) ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq13 eq84 | exact mod_symm (superpose eq13 eq84) | exact superpose eq84 eq13 | exact mod_symm (superpose eq84 eq13)
  have eq276 (X0 X1 X2 X3 : G) : (w ((X1 ◇ (X2 ◇ X3)) ◇ X0) X2) = (w X3 (X0 ◇ X1)) := by first | exact superpose eq13 eq84 | exact mod_symm (superpose eq13 eq84) | exact superpose eq84 eq13 | exact mod_symm (superpose eq84 eq13)
  have eq525 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ (e (X1 ◇ X1))))) = (w (v X2) ((v X0) ◇ (e X1))) := by first | exact superpose eq50 eq49 | exact mod_symm (superpose eq50 eq49) | exact superpose eq49 eq50 | exact mod_symm (superpose eq49 eq50)
  have eq528 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ (e (X1 ◇ X1))))) = (w (v X2) ((v X0) ◇ X1)) := by first | exact superpose eq115 eq525 | exact mod_symm (superpose eq115 eq525) | exact superpose eq525 eq115 | exact mod_symm (superpose eq525 eq115)
  have eq542 (X0 X1 X2 : G) : (w (v X2) ((v X0) ◇ X1)) = (v (w X2 (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq115 eq528 | exact mod_symm (superpose eq115 eq528) | exact superpose eq528 eq115 | exact mod_symm (superpose eq528 eq115)
  have eq621 (X0 X1 : G) : (w (e (X0 ◇ X0)) X1) = (e ((e X0) ◇ (v X1))) := by first | exact superpose eq51 eq20 | exact mod_symm (superpose eq51 eq20) | exact superpose eq20 eq51 | exact mod_symm (superpose eq20 eq51)
  have eq638 (X0 X1 : G) : (w (e (X0 ◇ X0)) X1) = (e (X0 ◇ (v X1))) := by first | exact superpose eq40 eq621 | exact mod_symm (superpose eq40 eq621) | exact superpose eq621 eq40 | exact mod_symm (superpose eq621 eq40)
  have eq655 (X0 X1 : G) : (w (X0 ◇ X0) X1) = (e (X0 ◇ (v X1))) := by first | exact superpose eq102 eq638 | exact mod_symm (superpose eq102 eq638) | exact superpose eq638 eq102 | exact mod_symm (superpose eq638 eq102)
  have eq767 (X0 X1 X2 : G) : ((w X0 X1) ◇ (e (v X2))) = (e (v ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq15 eq32 | exact mod_symm (superpose eq15 eq32) | exact superpose eq32 eq15 | exact mod_symm (superpose eq32 eq15)
  have eq806 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = ((w X0 X1) ◇ (e (v X2))) := by first | exact superpose eq20 eq767 | exact mod_symm (superpose eq20 eq767) | exact superpose eq767 eq20 | exact mod_symm (superpose eq767 eq20)
  have eq829 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = (e ((w X0 X1) ◇ (v X2))) := by first | exact superpose eq54 eq806 | exact mod_symm (superpose eq54 eq806) | exact superpose eq806 eq54 | exact mod_symm (superpose eq806 eq54)
  have eq1484 (X0 X1 X2 : G) : (v (w X0 (X1 ◇ X2))) = (w (v X0) (w X1 X2)) := by first | exact superpose eq99 eq49 | exact mod_symm (superpose eq99 eq49) | exact superpose eq49 eq99 | exact mod_symm (superpose eq49 eq99)
  have eq1556 (X0 X1 X2 X3 : G) : (w X2 (X0 ◇ X1)) = (w ((X2 ◇ X3) ◇ X0) (X3 ◇ X1)) := by first | exact superpose eq81 eq84 | exact mod_symm (superpose eq81 eq84) | exact superpose eq84 eq81 | exact mod_symm (superpose eq84 eq81)
  have eq1704 (X0 X1 X2 X3 : G) : (w X3 (X2 ◇ (X3 ◇ X0))) = (w X1 (X0 ◇ (X1 ◇ X2))) := by first | exact superpose eq82 eq84 | exact mod_symm (superpose eq82 eq84) | exact superpose eq84 eq82 | exact mod_symm (superpose eq84 eq82)
  have eq1750 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ (e (X0 ◇ X1)))) = (w X2 (X3 ◇ ((e X0) ◇ X1))) := by first | exact superpose eq40 eq115 | exact mod_symm (superpose eq40 eq115) | exact superpose eq115 eq40 | exact mod_symm (superpose eq115 eq40)
  have eq1802 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((e X0) ◇ X1))) = (w X2 (X3 ◇ (X0 ◇ X1))) := by first | exact superpose eq115 eq1750 | exact mod_symm (superpose eq115 eq1750) | exact superpose eq1750 eq115 | exact mod_symm (superpose eq1750 eq115)
  have eq1991 (X0 X1 X2 X3 : G) : ((w X0 X1) ◇ (w X2 X3)) = (e ((w X0 X1) ◇ (w X2 X3))) := by first | exact superpose eq29 eq53 | exact mod_symm (superpose eq29 eq53) | exact superpose eq53 eq29 | exact mod_symm (superpose eq53 eq29)
  have eq2585 (X0 X1 X2 X3 : G) : (w (X0 ◇ X1) (X2 ◇ X3)) = ((e (w X0 X1)) ◇ (w X2 X3)) := by first | exact superpose eq829 eq34 | exact mod_symm (superpose eq829 eq34) | exact superpose eq34 eq829 | exact mod_symm (superpose eq34 eq829)
  have eq2620 (X0 X1 X2 X3 : G) : (e ((w X0 X1) ◇ (w X2 X3))) = (w (X0 ◇ X1) (X2 ◇ X3)) := by first | exact superpose eq53 eq2585 | exact mod_symm (superpose eq53 eq2585) | exact superpose eq2585 eq53 | exact mod_symm (superpose eq2585 eq53)
  have eq2650 (X0 X1 X2 X3 : G) : ((w X0 X1) ◇ (w X2 X3)) = (w (X0 ◇ X1) (X2 ◇ X3)) := by first | exact superpose eq1991 eq2620 | exact mod_symm (superpose eq1991 eq2620) | exact superpose eq2620 eq1991 | exact mod_symm (superpose eq2620 eq1991)
  have eq3753 (X0 X1 X2 X3 X4 : G) : (w X3 (X4 ◇ ((X0 ◇ (e X1)) ◇ X2))) = (w X3 (X4 ◇ (e ((X0 ◇ X1) ◇ X2)))) := by first | exact superpose eq119 eq115 | exact mod_symm (superpose eq119 eq115) | exact superpose eq115 eq119 | exact mod_symm (superpose eq115 eq119)
  have eq3764 (X0 X1 X2 X3 X4 : G) : (w X3 (X4 ◇ ((X0 ◇ (e X1)) ◇ X2))) = (w X3 (X4 ◇ ((X0 ◇ X1) ◇ X2))) := by first | exact superpose eq115 eq3753 | exact mod_symm (superpose eq115 eq3753) | exact superpose eq3753 eq115 | exact mod_symm (superpose eq3753 eq115)
  have eq4268 (X0 X1 X2 X3 : G) : (w (w X0 X1) (w X2 X3)) = (v (w (X0 ◇ X1) (X2 ◇ X3))) := by first | exact superpose eq1484 eq101 | exact mod_symm (superpose eq1484 eq101) | exact superpose eq101 eq1484 | exact mod_symm (superpose eq101 eq1484)
  have eq4285 (X0 X1 X2 X3 : G) : (w (w X0 X1) (w X2 X3)) = (v ((w X0 X1) ◇ (w X2 X3))) := by first | exact superpose eq2650 eq4268 | exact mod_symm (superpose eq2650 eq4268) | exact superpose eq4268 eq2650 | exact mod_symm (superpose eq4268 eq2650)
  have eq6712 (X0 X1 X2 X3 X4 : G) : (w X0 (X4 ◇ ((X2 ◇ X1) ◇ X3))) = (w ((X0 ◇ X1) ◇ X4) (X3 ◇ X2)) := by first | exact superpose eq81 eq276 | exact mod_symm (superpose eq81 eq276) | exact superpose eq276 eq81 | exact mod_symm (superpose eq276 eq81)
  have eq6793 (X0 X1 X2 X3 X4 : G) : (w X0 (X4 ◇ ((X2 ◇ X1) ◇ X3))) = ((w (X0 ◇ X1) X4) ◇ (w X3 X2)) := by first | exact superpose eq2650 eq6712 | exact mod_symm (superpose eq2650 eq6712) | exact superpose eq6712 eq2650 | exact mod_symm (superpose eq6712 eq2650)
  have eq8397 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((e X1) ◇ X0))) = (w ((X2 ◇ (e (v X1))) ◇ X3) (X0 ◇ (e (v X1)))) := by first | exact superpose eq85 eq1556 | exact mod_symm (superpose eq85 eq1556) | exact superpose eq1556 eq85 | exact mod_symm (superpose eq1556 eq85)
  have eq8418 (X0 X1 X2 : G) : (w X0 (X1 ◇ X2)) = (w X2 (X1 ◇ X0)) := by first | exact superpose eq1556 eq275 | exact mod_symm (superpose eq1556 eq275) | exact superpose eq275 eq1556 | exact mod_symm (superpose eq275 eq1556)
  have eq8483 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((e X1) ◇ X0))) = (w ((X2 ◇ (e (v X1))) ◇ X3) (X0 ◇ (v X1))) := by first | exact superpose eq115 eq8397 | exact mod_symm (superpose eq115 eq8397) | exact superpose eq8397 eq115 | exact mod_symm (superpose eq8397 eq115)
  have eq8526 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((e X1) ◇ X0))) = (w (v X1) (X0 ◇ ((X2 ◇ (e (v X1))) ◇ X3))) := by first | exact superpose eq8418 eq8483 | exact mod_symm (superpose eq8418 eq8483) | exact superpose eq8483 eq8418 | exact mod_symm (superpose eq8483 eq8418)
  have eq8553 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((e X1) ◇ X0))) = (w (v X1) (X0 ◇ ((X2 ◇ (v X1)) ◇ X3))) := by first | exact superpose eq3764 eq8526 | exact mod_symm (superpose eq3764 eq8526) | exact superpose eq8526 eq3764 | exact mod_symm (superpose eq8526 eq3764)
  have eq8566 (X0 X1 X2 X3 : G) : ((w ((v X1) ◇ (v X1)) X0) ◇ (w X3 X2)) = (w X2 (X3 ◇ ((e X1) ◇ X0))) := by first | exact superpose eq6793 eq8553 | exact mod_symm (superpose eq6793 eq8553) | exact superpose eq8553 eq6793 | exact mod_symm (superpose eq8553 eq6793)
  have eq8573 (X0 X1 X2 X3 : G) : ((w ((v X1) ◇ (v X1)) X0) ◇ (w X3 X2)) = (w X2 (X3 ◇ (X1 ◇ X0))) := by first | exact superpose eq1802 eq8566 | exact mod_symm (superpose eq1802 eq8566) | exact superpose eq8566 eq1802 | exact mod_symm (superpose eq8566 eq1802)
  have eq8575 (X0 X1 X2 X3 : G) : ((e ((v X1) ◇ (v X0))) ◇ (w X3 X2)) = (w X2 (X3 ◇ (X1 ◇ X0))) := by first | exact superpose eq655 eq8573 | exact mod_symm (superpose eq655 eq8573) | exact superpose eq8573 eq655 | exact mod_symm (superpose eq8573 eq655)
  have eq8576 (X0 X1 X2 X3 : G) : (e (((v X1) ◇ (v X0)) ◇ (w X3 X2))) = (w X2 (X3 ◇ (X1 ◇ X0))) := by first | exact superpose eq53 eq8575 | exact mod_symm (superpose eq53 eq8575) | exact superpose eq8575 eq53 | exact mod_symm (superpose eq8575 eq53)
  have eq8577 (X0 X1 X2 X3 : G) : (e ((v (X1 ◇ X0)) ◇ (w X3 X2))) = (w X2 (X3 ◇ (X1 ◇ X0))) := by first | exact superpose eq15 eq8576 | exact mod_symm (superpose eq15 eq8576) | exact superpose eq8576 eq15 | exact mod_symm (superpose eq8576 eq15)
  have eq8578 (X0 X1 X2 X3 : G) : ((w X1 X0) ◇ (e (w X3 X2))) = (w X2 (X3 ◇ (X1 ◇ X0))) := by first | exact superpose eq32 eq8577 | exact mod_symm (superpose eq32 eq8577) | exact superpose eq8577 eq32 | exact mod_symm (superpose eq8577 eq32)
  have eq8579 (X0 X1 X2 X3 : G) : (e ((w X1 X0) ◇ (w X3 X2))) = (w X2 (X3 ◇ (X1 ◇ X0))) := by first | exact superpose eq54 eq8578 | exact mod_symm (superpose eq54 eq8578) | exact superpose eq8578 eq54 | exact mod_symm (superpose eq8578 eq54)
  have eq8580 (X0 X1 X2 X3 : G) : ((w X1 X0) ◇ (w X3 X2)) = (w X2 (X3 ◇ (X1 ◇ X0))) := by first | exact superpose eq1991 eq8579 | exact mod_symm (superpose eq1991 eq8579) | exact superpose eq8579 eq1991 | exact mod_symm (superpose eq8579 eq1991)
  have eq15556 (X0 X1 X2 : G) : (v (w X0 (X1 ◇ (X0 ◇ X2)))) = (w (v X1) ((v X2) ◇ X1)) := by first | exact superpose eq1704 eq542 | exact mod_symm (superpose eq1704 eq542) | exact superpose eq542 eq1704 | exact mod_symm (superpose eq542 eq1704)
  have eq15686 (X0 X1 X2 : G) : (v (w X0 (X1 ◇ (X0 ◇ X2)))) = (w X1 ((v X2) ◇ (v X1))) := by first | exact superpose eq8418 eq15556 | exact mod_symm (superpose eq8418 eq15556) | exact superpose eq15556 eq8418 | exact mod_symm (superpose eq15556 eq8418)
  have eq15776 (X0 X1 X2 : G) : (v (w X0 (X1 ◇ (X0 ◇ X2)))) = (w X1 (v (X2 ◇ X1))) := by first | exact superpose eq15 eq15686 | exact mod_symm (superpose eq15 eq15686) | exact superpose eq15686 eq15 | exact mod_symm (superpose eq15686 eq15)
  have eq15862 (X0 X1 X2 : G) : (v (w X0 (X1 ◇ (X0 ◇ X2)))) = (w X1 (w X2 X1)) := by first | exact superpose eq99 eq15776 | exact mod_symm (superpose eq99 eq15776) | exact superpose eq15776 eq99 | exact mod_symm (superpose eq15776 eq99)
  have eq15937 (X0 X1 X2 : G) : (v ((w X0 X2) ◇ (w X1 X0))) = (w X1 (w X2 X1)) := by first | exact superpose eq8580 eq15862 | exact mod_symm (superpose eq8580 eq15862) | exact superpose eq15862 eq8580 | exact mod_symm (superpose eq15862 eq8580)
  have eq15992 (X0 X1 X2 : G) : (w (w X0 X2) (w X1 X0)) = (w X1 (w X2 X1)) := by first | exact superpose eq4285 eq15937 | exact mod_symm (superpose eq4285 eq15937) | exact superpose eq15937 eq4285 | exact mod_symm (superpose eq15937 eq4285)
  have eq44316 : (w x x) ≠ (w x (w x x)) := by first | exact superpose eq15992 eq21 | exact mod_symm (superpose eq15992 eq21) | exact superpose eq21 eq15992 | exact mod_symm (superpose eq21 eq15992)
  have eq44464 : (e x) ≠ (w x (e x)) := by first | exact superpose eq42 eq44316 | exact mod_symm (superpose eq42 eq44316) | exact superpose eq44316 eq42 | exact mod_symm (superpose eq44316 eq42)
  have eq44696 : (w x x) ≠ (e x) := by first | exact superpose eq100 eq44464 | exact mod_symm (superpose eq100 eq44464) | exact superpose eq44464 eq100 | exact mod_symm (superpose eq44464 eq100)
  subsumption eq44696 eq42


/-- Equation 4443 `x ◇ (y ◇ x) = (y ◇ x) ◇ y` is term-definable from equation 3607 over finite magmas, via the term
`x □ y := u^[2N+1] (x ◇ y)` with `u a = (a ◇ a)`. -/
private theorem aux3607_4443 [Magma G] (h : Equation3607 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a)
    (hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a)
    (hw : ∀ a b : G, w a b = (e (v ((a ◇ b)))))
    (x y : G) :
    (w x (w y x)) =
      (w (w y x) y) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ X1))) := mod_symm (hw ..)
  have eq21 : (w x (w y x)) ≠ (w (w y x) y) := mod_symm nh
  have eq28 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq29 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq31 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq33 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq36 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v (e (X0 ◇ X1)))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq37 (X0 X1 : G) : (e (e (v (X0 ◇ X1)))) = (w (e X0) (e X1)) := by first | exact superpose eq17 eq36 | exact mod_symm (superpose eq17 eq36) | exact superpose eq36 eq17 | exact mod_symm (superpose eq36 eq17)
  have eq39 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq40 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq31 | exact mod_symm (superpose eq14 eq31) | exact superpose eq31 eq14 | exact mod_symm (superpose eq31 eq14)
  have eq41 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq16 eq37 | exact mod_symm (superpose eq16 eq37) | exact superpose eq37 eq16 | exact mod_symm (superpose eq37 eq16)
  have eq43 (X0 X1 : G) : (w X0 X1) = (w (e X0) (e X1)) := by first | exact superpose eq20 eq41 | exact mod_symm (superpose eq20 eq41) | exact superpose eq41 eq20 | exact mod_symm (superpose eq41 eq20)
  have eq45 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq48 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (w (v X0) (v X1)) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq49 (X0 X1 : G) : (v (w X0 X1)) = (w (v X0) (v X1)) := by first | exact superpose eq28 eq48 | exact mod_symm (superpose eq28 eq48) | exact superpose eq48 eq28 | exact mod_symm (superpose eq48 eq28)
  have eq51 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq45 | exact mod_symm (superpose eq14 eq45) | exact superpose eq45 eq14 | exact mod_symm (superpose eq45 eq14)
  have eq81 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq83 (X0 X1 X2 : G) : (e (v (X0 ◇ X1))) = (w X2 ((X1 ◇ X2) ◇ X0)) := by first | exact superpose eq13 eq20 | exact mod_symm (superpose eq13 eq20) | exact superpose eq20 eq13 | exact mod_symm (superpose eq20 eq13)
  have eq84 (X0 X1 X2 : G) : (w X0 X1) = (w X2 ((X1 ◇ X2) ◇ X0)) := by first | exact superpose eq20 eq83 | exact mod_symm (superpose eq20 eq83) | exact superpose eq83 eq20 | exact mod_symm (superpose eq83 eq20)
  have eq86 (X0 X1 : G) : (w (e X0) (e X1)) = (w (e X0) X1) := by first | exact superpose eq16 eq43 | exact mod_symm (superpose eq16 eq43) | exact superpose eq43 eq16 | exact mod_symm (superpose eq43 eq16)
  have eq87 (X0 X1 X2 : G) : (w (v (X0 ◇ X1)) X2) = (w (w X0 X1) (e X2)) := by first | exact superpose eq20 eq43 | exact mod_symm (superpose eq20 eq43) | exact superpose eq43 eq20 | exact mod_symm (superpose eq43 eq20)
  have eq88 (X0 X1 X2 : G) : (w (w X0 X1) (e X2)) = (w (w X0 X1) X2) := by first | exact superpose eq29 eq43 | exact mod_symm (superpose eq29 eq43) | exact superpose eq43 eq29 | exact mod_symm (superpose eq43 eq29)
  have eq89 (X0 X1 : G) : (w X1 (e X0)) = (w (e X1) (e X0)) := by first | exact superpose eq16 eq43 | exact mod_symm (superpose eq16 eq43) | exact superpose eq43 eq16 | exact mod_symm (superpose eq43 eq16)
  have eq90 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w (e X2) (w X0 X1)) := by first | exact superpose eq20 eq43 | exact mod_symm (superpose eq20 eq43) | exact superpose eq43 eq20 | exact mod_symm (superpose eq43 eq20)
  have eq91 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq29 eq43 | exact mod_symm (superpose eq29 eq43) | exact superpose eq43 eq29 | exact mod_symm (superpose eq43 eq29)
  have eq99 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w X2 (w X0 X1)) := by first | exact superpose eq91 eq90 | exact mod_symm (superpose eq91 eq90) | exact superpose eq90 eq91 | exact mod_symm (superpose eq90 eq91)
  have eq100 (X0 X1 : G) : (w X1 X0) = (w X1 (e X0)) := by first | exact superpose eq43 eq89 | exact mod_symm (superpose eq43 eq89) | exact superpose eq89 eq43 | exact mod_symm (superpose eq89 eq43)
  have eq101 (X0 X1 X2 : G) : (w (v (X0 ◇ X1)) X2) = (w (w X0 X1) X2) := by first | exact superpose eq88 eq87 | exact mod_symm (superpose eq88 eq87) | exact superpose eq87 eq88 | exact mod_symm (superpose eq87 eq88)
  have eq102 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq43 eq86 | exact mod_symm (superpose eq43 eq86) | exact superpose eq86 eq43 | exact mod_symm (superpose eq86 eq43)
  have eq113 (X0 X1 X2 : G) : (w (X0 ◇ (e X1)) X2) = (w (e (X0 ◇ X1)) (e X2)) := by first | exact superpose eq39 eq43 | exact mod_symm (superpose eq39 eq43) | exact superpose eq43 eq39 | exact mod_symm (superpose eq43 eq39)
  have eq114 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w (e X2) (e (X0 ◇ X1))) := by first | exact superpose eq39 eq43 | exact mod_symm (superpose eq39 eq43) | exact superpose eq43 eq39 | exact mod_symm (superpose eq43 eq39)
  have eq115 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq43 eq114 | exact mod_symm (superpose eq43 eq114) | exact superpose eq114 eq43 | exact mod_symm (superpose eq114 eq43)
  have eq116 (X0 X1 X2 : G) : (w (X0 ◇ (e X1)) X2) = (w (X0 ◇ X1) X2) := by first | exact superpose eq43 eq113 | exact mod_symm (superpose eq43 eq113) | exact superpose eq113 eq43 | exact mod_symm (superpose eq113 eq43)
  have eq155 (X0 X1 X2 : G) : (w (e (X0 ◇ X1)) (e X2)) = (w ((e X0) ◇ X1) X2) := by first | exact superpose eq40 eq43 | exact mod_symm (superpose eq40 eq43) | exact superpose eq43 eq40 | exact mod_symm (superpose eq43 eq40)
  have eq157 (X0 X1 X2 : G) : (w X2 (e (X0 ◇ X1))) = (w X2 ((e X0) ◇ X1)) := by first | exact superpose eq40 eq100 | exact mod_symm (superpose eq40 eq100) | exact superpose eq100 eq40 | exact mod_symm (superpose eq100 eq40)
  have eq158 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X2 ((e X0) ◇ X1)) := by first | exact superpose eq100 eq157 | exact mod_symm (superpose eq100 eq157) | exact superpose eq157 eq100 | exact mod_symm (superpose eq157 eq100)
  have eq160 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = (w ((e X0) ◇ X1) X2) := by first | exact superpose eq43 eq155 | exact mod_symm (superpose eq43 eq155) | exact superpose eq155 eq43 | exact mod_symm (superpose eq155 eq43)
  have eq195 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w (e X0) (v X1)) := by first | exact superpose eq19 eq49 | exact mod_symm (superpose eq19 eq49) | exact superpose eq49 eq19 | exact mod_symm (superpose eq49 eq19)
  have eq197 (X0 X1 : G) : (v (w X1 ((e X0) ◇ (e X0)))) = (w (v X1) (e X0)) := by first | exact superpose eq19 eq49 | exact mod_symm (superpose eq19 eq49) | exact superpose eq49 eq19 | exact mod_symm (superpose eq49 eq19)
  have eq203 (X0 X1 : G) : (v (w X1 ((e X0) ◇ (e X0)))) = (w (v X1) X0) := by first | exact superpose eq100 eq197 | exact mod_symm (superpose eq100 eq197) | exact superpose eq197 eq100 | exact mod_symm (superpose eq197 eq100)
  have eq205 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w X0 (v X1)) := by first | exact superpose eq102 eq195 | exact mod_symm (superpose eq102 eq195) | exact superpose eq195 eq102 | exact mod_symm (superpose eq195 eq102)
  have eq207 (X0 X1 : G) : (w (v X1) X0) = (v (w X1 ((e X0) ◇ X0))) := by first | exact superpose eq115 eq203 | exact mod_symm (superpose eq115 eq203) | exact superpose eq203 eq115 | exact mod_symm (superpose eq203 eq115)
  have eq209 (X0 X1 : G) : (w X0 (v X1)) = (v (w ((e X0) ◇ X0) X1)) := by first | exact superpose eq116 eq205 | exact mod_symm (superpose eq116 eq205) | exact superpose eq205 eq116 | exact mod_symm (superpose eq205 eq116)
  have eq211 (X0 X1 : G) : (w (v X1) X0) = (v (w X1 (X0 ◇ X0))) := by first | exact superpose eq158 eq207 | exact mod_symm (superpose eq158 eq207) | exact superpose eq207 eq158 | exact mod_symm (superpose eq207 eq158)
  have eq212 (X0 X1 : G) : (w X0 (v X1)) = (v (w (X0 ◇ X0) X1)) := by first | exact superpose eq160 eq209 | exact mod_symm (superpose eq160 eq209) | exact superpose eq209 eq160 | exact mod_symm (superpose eq209 eq160)
  have eq625 (X0 X1 : G) : (w (e (X0 ◇ X0)) X1) = (e ((e X0) ◇ (v X1))) := by first | exact superpose eq51 eq20 | exact mod_symm (superpose eq51 eq20) | exact superpose eq20 eq51 | exact mod_symm (superpose eq20 eq51)
  have eq642 (X0 X1 : G) : (w (e (X0 ◇ X0)) X1) = (e (X0 ◇ (v X1))) := by first | exact superpose eq40 eq625 | exact mod_symm (superpose eq40 eq625) | exact superpose eq625 eq40 | exact mod_symm (superpose eq625 eq40)
  have eq659 (X0 X1 : G) : (w (X0 ◇ X0) X1) = (e (X0 ◇ (v X1))) := by first | exact superpose eq102 eq642 | exact mod_symm (superpose eq102 eq642) | exact superpose eq642 eq102 | exact mod_symm (superpose eq642 eq102)
  have eq1567 (X0 X1 : G) : (v (w X1 (X0 ◇ X0))) = (w (v X1) ((X0 ◇ X0) ◇ X0)) := by first | exact superpose eq81 eq211 | exact mod_symm (superpose eq81 eq211) | exact superpose eq211 eq81 | exact mod_symm (superpose eq211 eq81)
  have eq1584 (X0 X1 : G) : (w (v X1) X0) = (w (v X1) ((X0 ◇ X0) ◇ X0)) := by first | exact superpose eq211 eq1567 | exact mod_symm (superpose eq211 eq1567) | exact superpose eq1567 eq211 | exact mod_symm (superpose eq1567 eq211)
  have eq4493 (X0 X1 : G) : (w (e X0) X1) = (w (e X0) ((X1 ◇ X1) ◇ X1)) := by first | exact superpose eq19 eq1584 | exact mod_symm (superpose eq19 eq1584) | exact superpose eq1584 eq19 | exact mod_symm (superpose eq1584 eq19)
  have eq4546 (X0 X1 : G) : (w (e X0) X1) = (w X0 ((X1 ◇ X1) ◇ X1)) := by first | exact superpose eq102 eq4493 | exact mod_symm (superpose eq102 eq4493) | exact superpose eq4493 eq102 | exact mod_symm (superpose eq4493 eq102)
  have eq4561 (X0 X1 : G) : (w X0 X1) = (w X0 ((X1 ◇ X1) ◇ X1)) := by first | exact superpose eq102 eq4546 | exact mod_symm (superpose eq102 eq4546) | exact superpose eq4546 eq102 | exact mod_symm (superpose eq4546 eq102)
  have eq4805 (X0 X1 : G) : (v (w (X0 ◇ X0) X1)) = (w X0 (v ((X1 ◇ X1) ◇ X1))) := by first | exact superpose eq4561 eq212 | exact mod_symm (superpose eq4561 eq212) | exact superpose eq212 eq4561 | exact mod_symm (superpose eq212 eq4561)
  have eq4820 (X0 X1 : G) : (v (w (X0 ◇ X0) X1)) = (w X0 (w (X1 ◇ X1) X1)) := by first | exact superpose eq99 eq4805 | exact mod_symm (superpose eq99 eq4805) | exact superpose eq4805 eq99 | exact mod_symm (superpose eq4805 eq99)
  have eq4842 (X0 X1 : G) : (v (w (X0 ◇ X0) X1)) = (w X0 (e (X1 ◇ (v X1)))) := by first | exact superpose eq659 eq4820 | exact mod_symm (superpose eq659 eq4820) | exact superpose eq4820 eq659 | exact mod_symm (superpose eq4820 eq659)
  have eq4857 (X0 X1 : G) : (v (w (X0 ◇ X0) X1)) = (w X0 (X1 ◇ (v X1))) := by first | exact superpose eq100 eq4842 | exact mod_symm (superpose eq100 eq4842) | exact superpose eq4842 eq100 | exact mod_symm (superpose eq4842 eq100)
  have eq4871 (X0 X1 : G) : (w X0 (v X1)) = (w X0 (X1 ◇ (v X1))) := by first | exact superpose eq212 eq4857 | exact mod_symm (superpose eq212 eq4857) | exact superpose eq4857 eq212 | exact mod_symm (superpose eq4857 eq212)
  have eq5065 (X0 X1 : G) : (w X0 (v (X1 ◇ X0))) = (w (v (X1 ◇ X0)) X1) := by first | exact superpose eq4871 eq84 | exact mod_symm (superpose eq4871 eq84) | exact superpose eq84 eq4871 | exact mod_symm (superpose eq84 eq4871)
  have eq5109 (X0 X1 : G) : (w (w X1 X0) X1) = (w X0 (v (X1 ◇ X0))) := by first | exact superpose eq101 eq5065 | exact mod_symm (superpose eq101 eq5065) | exact superpose eq5065 eq101 | exact mod_symm (superpose eq5065 eq101)
  have eq5135 (X0 X1 : G) : (w X0 (w X1 X0)) = (w (w X1 X0) X1) := by first | exact superpose eq99 eq5109 | exact mod_symm (superpose eq99 eq5109) | exact superpose eq5109 eq99 | exact mod_symm (superpose eq5109 eq99)
  have eq5413 : (w x (w y x)) ≠ (w x (w y x)) := by first | exact superpose eq5135 eq21 | exact mod_symm (superpose eq5135 eq21) | exact superpose eq21 eq5135 | exact mod_symm (superpose eq21 eq5135)
  first | exact eq5413 rfl | exact eq5413 _ rfl | exact eq5413 _ _ rfl | exact eq5413 _ _ _ rfl


theorem Equation332_termDefinableFromFin_Equation3607 :
    Law332.TermDefinableFromFin Law3607 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (Term.var 0)))
    (fun G ↦ (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0)))) 2 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation3607 G := Law3607.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ endo3607_0 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law332.models_iff]
  intro x y
  exact aux3607_332 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation3342_termDefinableFromFin_Equation3607 :
    Law3342.TermDefinableFromFin Law3607 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (Term.var 0)))
    (fun G ↦ (tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 1))) (Term.var 1))) 3 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation3607 G := Law3607.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ endo3607_0 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law3342.models_iff]
  intro x y
  exact aux3607_3342 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation3545_termDefinableFromFin_Equation3607 :
    Law3545.TermDefinableFromFin Law3607 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (Term.var 0)))
    (fun G ↦ (tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 1))) (Term.var 1))) 3 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation3607 G := Law3607.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ endo3607_0 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law3545.models_iff]
  intro x y
  exact aux3607_3545 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation3675_termDefinableFromFin_Equation3607 :
    Law3675.TermDefinableFromFin Law3607 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (Term.var 0)))
    (fun G ↦ (tm (Term.var 0) (Term.var 1))) 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation3607 G := Law3607.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ endo3607_0 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law3675.models_iff]
  intro x y
  exact aux3607_3675 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation4443_termDefinableFromFin_Equation3607 :
    Law4443.TermDefinableFromFin Law3607 := by
  refine termDefinableFromFin_of_iterate_ev (fun G ↦ (tm1 (Term.var 0) (Term.var 0)))
    (fun G ↦ (tm (Term.var 0) (Term.var 1))) 1 ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation3607 G := Law3607.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ endo3607_0 h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, ((v (e a)) ◇ (v (e a))) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v ((e a) ◇ (e a)) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law4443.models_iff]
  intro x y
  exact aux3607_4443 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

end Law.MagmaLaw
