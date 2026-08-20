import equational_theories.Definability.Basic
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Term-definability facts with a witness too large to guess

`Definability/PositiveTerms.lean` collects the cells whose defining term a syntactic enumeration
could reach; five leaves is about where that stops, because the number of terms grows faster than
the number of distinct operations they compute. The cells here were found the other way round. Fix
a handful of finite models of the source law, close the set of binary operations on their product
under the source operation while remembering one term per operation, and the closure is finite even
though the terms in it are not bounded -- so a witness of seven leaves costs no more to find than a
witness of three. Whatever a candidate fails on becomes another factor of the product, and the loop
repeats until the candidate survives every model of the source in the bank.

Each cell contributes a `private` lemma carrying the equational content `s ⊢ t[◇ := w]`, replayed
from a Vampire refutation, and a packaging theorem naming the term. The witness enters the lemma as
an abstract `wf` pinned by `hwdef` rather than unfolded, since substituting it into the target would
otherwise give a goal several times the size of either.
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

set_option maxHeartbeats 1400000 in
/-- Equation 667 `x = y ◇ (x ◇ ((x ◇ x) ◇ y))` holds of the operation
`x □ y := ((((x*y)*(x*x))*(x*y))*(y*x))` in every magma satisfying equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. -/
private theorem aux898_667 [Magma G] (h : Equation898 G) (wf : G → G → G)
    (hwdef : ∀ a b : G, wf a b = (((a ◇ b) ◇ (a ◇ a)) ◇ (a ◇ b)) ◇ (b ◇ a)) (x y : G) :
    x = wf y (wf x (wf (wf x x) y)) := by
  by_contra nh
  have ef6 : x ≠ wf y (wf x (wf (wf x x) y)) := mod_symm nh
  have ef7 (X0 X1 : G) :
      wf X0 X1 = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ (((X0 ◇ X3) ◇ (X3 ◇ X2)) ◇ X1)) = X2 := by
    first | exact superpose ef8 ef8
  have ef10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0) = X3 := by
    first | exact superpose ef8 ef8
  have ef11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0 = X2 := by
    first | exact superpose ef8 ef8
  have ef15 :
      x ≠ (((y ◇ (wf x (wf (wf x x) y))) ◇ (y ◇ y)) ◇ (y ◇ (wf x (wf (wf x x) y)))) ◇
      ((wf x (wf (wf x x) y)) ◇ y) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef16 :
      x ≠ (((y ◇
      ((((x ◇ (wf (wf x x) y)) ◇ (x ◇ x)) ◇ (x ◇ (wf (wf x x) y))) ◇ ((wf (wf x x) y) ◇ x))) ◇ (y ◇
      y)) ◇ (y ◇ ((((x ◇ (wf (wf x x) y)) ◇ (x ◇ x)) ◇ (x ◇ (wf (wf x x) y))) ◇
      ((wf (wf x x) y) ◇ x)))) ◇ (((((x ◇ (wf (wf x x) y)) ◇ (x ◇ x)) ◇ (x ◇ (wf (wf x x) y))) ◇
      ((wf (wf x x) y) ◇ x)) ◇ y) := by
    first | exact superpose ef7 ef15 | exact superpose ef15 ef7
  have ef20 :
      x ≠ (((y ◇
      ((((x ◇ (((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇ (y ◇ (wf x x)))) ◇ (x ◇ x)) ◇
      (x ◇ (((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇ (y ◇ (wf x x))))) ◇
      ((((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇ (y ◇ (wf x x))) ◇ x))) ◇ (y ◇
      y)) ◇ (y ◇
      ((((x ◇ (((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇ (y ◇ (wf x x)))) ◇
      (x ◇ x)) ◇ (x ◇
      (((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇ (y ◇ (wf x x))))) ◇
      ((((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇ (y ◇ (wf x x))) ◇ x)))) ◇
      (((((x ◇ (((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇ (y ◇ (wf x x)))) ◇
      (x ◇ x)) ◇ (x ◇ (((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇
      (y ◇ (wf x x))))) ◇ ((((((wf x x) ◇ y) ◇ ((wf x x) ◇ (wf x x))) ◇ ((wf x x) ◇ y)) ◇ (y ◇
      (wf x x))) ◇ x)) ◇ y) := by
    first | exact superpose ef7 ef16 | exact superpose ef16 ef7
  have ef24 :
      x ≠ (((y ◇
      ((((x ◇ ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ (x ◇ x)) ◇
      (x ◇ ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      (((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      x))) ◇ (y ◇ y)) ◇ (y ◇
      ((((x ◇ ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (x ◇ x)) ◇ (x ◇
      ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      (((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇
      (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ x)))) ◇ (((((x ◇
      ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (x ◇ x)) ◇ (x ◇
      ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇
      (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      (((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)) ◇ (y ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ x)) ◇ y) := by
    first | exact superpose ef7 ef20 | exact superpose ef20 ef7
  have ef29 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X2 := by
    first | exact superpose ef11 ef11
  have ef30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1) = X2 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef31 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2)) = (X1 ◇ X0) ◇ X3 := by
    first | exact superpose ef11 ef11
  have ef33 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ (X3 ◇ X2)) = X1 ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef35 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X2 := by
    first | exact superpose ef11 ef30 | exact superpose ef30 ef11
  have ef36 (X0 X1 X2 X3 : G) : X2 ◇ X1 = (X0 ◇ X3) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2)) := by
    first | exact superpose ef30 ef30
  have ef40 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X2 := by
    first | exact superpose ef11 ef30 | exact superpose ef30 ef11
  have ef41 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef30 ef30
  have ef42 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef30 ef11 | exact superpose ef11 ef30
  have ef43 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef30 ef8 | exact superpose ef8 ef30
  have ef49 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) ◇ (X4 ◇ X3) = X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef55 (X0 X1 X2 X3 X4 : G) : X1 ◇ (X2 ◇ (X0 ◇ X1)) = ((X3 ◇ X4) ◇ (X4 ◇ X0)) ◇ (X2 ◇ X3) := by
    first | exact superpose ef9 ef9
  have ef72 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X4 := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef77 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X0) ◇ ((X4 ◇ X3) ◇ X1) = X4 := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef89 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X3 := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef96 (X0 X1 X2 X3 : G) : X2 ◇ X3 = X0 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef10 ef30 | exact superpose ef30 ef10
  have ef98 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X2 ◇ X3) = (X1 ◇ X0) ◇ (X0 ◇ X3) := by
    first | exact superpose ef10 ef11 | exact superpose ef11 ef10
  have ef191 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3 := by
    first | exact superpose ef29 ef11 | exact superpose ef11 ef29
  have ef217 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef30 ef31 | exact superpose ef31 ef30
  have ef290 (X0 : G) :
      x ≠ (((y ◇
      ((((x ◇ (X0 ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0)))) ◇ (x ◇ x)) ◇
      (x ◇ (X0 ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0))))) ◇
      ((X0 ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0))) ◇
      x))) ◇ (y ◇ y)) ◇ (y ◇
      ((((x ◇ (X0 ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0)))) ◇
      (x ◇ x)) ◇ (x ◇
      (X0 ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0))))) ◇
      ((X0 ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0))) ◇
      x)))) ◇ (((((x ◇
      (X0 ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0)))) ◇
      (x ◇ x)) ◇ (x ◇ (X0 ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0))))) ◇
      ((X0 ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇
      (((y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ X0))) ◇
      x)) ◇ y) := by
    first | exact superpose ef31 ef24 | exact superpose ef24 ef31
  have ef3504 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇ (x ◇ x)) ◇
      (x ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ (y ◇
      ((((x ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      (x ◇ x)) ◇ (x ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇
      x)))) ◇ (((((x ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      (x ◇ x)) ◇ (x ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      y) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇ x)) ◇ y) := by
    first | exact superpose ef42 ef290 | exact superpose ef290 ef42
  have ef6339 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇ (x ◇ x)) ◇
      (x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ (y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      (x ◇ x)) ◇ (x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇
      x)))) ◇ (((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      (x ◇ x)) ◇ (x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇ x)) ◇ y) := by
    first | exact superpose ef217 ef3504 | exact superpose ef3504 ef217
  have ef6650 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇ (x ◇ x)) ◇
      (x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      (x ◇ x)) ◇ (x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      (x ◇ x)) ◇ (x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))))) ◇
      ((((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef6339 | exact superpose ef6339 ef217
  have ef7305 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef6650 | exact superpose ef6650 ef217
  have ef7938 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)))) ◇
      x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)))) ◇
      ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef7305 | exact superpose ef7305 ef217
  have ef8566 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef7938 | exact superpose ef7938 ef217
  have ef9194 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef8566 | exact superpose ef8566 ef217
  have ef9822 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef9194 | exact superpose ef9194 ef217
  have ef10450 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef9822 | exact superpose ef9822 ef217
  have ef11076 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef41 ef10450 | exact superpose ef10450 ef41
  have ef11695 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef11076 | exact superpose ef11076 ef217
  have ef12305 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef11695 | exact superpose ef11695 ef217
  have ef12904 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇
      (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef30 ef12305 | exact superpose ef12305 ef30
  have ef13470 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef191 ef12904 | exact superpose ef12904 ef191
  have ef13996 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef13470 | exact superpose ef13470 ef217
  have ef14492 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef13996 | exact superpose ef13996 ef217
  have ef14975 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef41 ef14492 | exact superpose ef14492 ef41
  have ef15451 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef14975 | exact superpose ef14975 ef217
  have ef15907 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef15451 | exact superpose ef15451 ef217
  have ef16356 :
      x ≠ (((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇ (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef30 ef15907 | exact superpose ef15907 ef30
  have ef16797 :
      x ≠ (((y ◇
      ((((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇
      x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ ((y ◇
      ((((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef191 ef16356 | exact superpose ef16356 ef191
  have ef17222 :
      x ≠ (((y ◇
      ((((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇ (x ◇
      x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ ((y ◇
      ((((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef16797 | exact superpose ef16797 ef217
  have ef17633 :
      x ≠ (((y ◇
      ((((x ◇ x) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇ ((x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ ((y ◇ ((((x ◇ x) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇ ((x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef17222 | exact superpose ef17222 ef217
  have ef18013 :
      x ≠ (((y ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (y ◇ (y ◇ y)))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x) ◇
      (y ◇ (y ◇ y)))) ◇ ((x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      x))) ◇ y) := by
    first | exact superpose ef217 ef17633 | exact superpose ef17633 ef217
  have ef18378 :
      x ≠ (((y ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      (x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x) ◇ (y ◇ (y ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇
      x) ◇ (y ◇ (y ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x) ◇
      (y ◇ (y ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef217 ef18013 | exact superpose ef18013 ef217
  have ef18720 :
      x ≠ (((y ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      (x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (y ◇ (y ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (y ◇
      (y ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇
      (y ◇ (y ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef191 ef18378 | exact superpose ef18378 ef191
  have ef19031 :
      x ≠ (((y ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      (x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (y ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (y ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (y ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef217 ef18720 | exact superpose ef18720 ef217
  have ef19314 :
      x ≠ (((y ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      (x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (y ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (y ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (y ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef217 ef19031 | exact superpose ef19031 ef217
  have ef19574 :
      x ≠ (((y ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      (x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇
      (((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef217 ef19314 | exact superpose ef19314 ef217
  have ef19772 :
      x ≠ (((y ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇
      (x ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) ◇ (x ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef217 ef19574 | exact superpose ef19574 ef217
  have ef19944 :
      x ≠ (((y ◇ ((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇
      x))) ◇ (y ◇ y)) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef217 ef19772 | exact superpose ef19772 ef217
  have ef20090 :
      x ≠ (((y ◇ y) ◇ (((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇
      x)) ◇ y)) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef217 ef19944 | exact superpose ef19944 ef217
  have ef20230 :
      x ≠ (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))))) ◇
      ((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇
      x)) ◇ y) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ ((y ◇ ((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x))) ◇ y) := by
    first | exact superpose ef217 ef20090 | exact superpose ef20090 ef217
  have ef20352 :
      x ≠ (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))))) ◇
      (y ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x)))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇
      x)) ◇ y) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x)) ◇ y) := by
    first | exact superpose ef217 ef20230 | exact superpose ef20230 ef217
  have ef20448 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x)))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇
      x)) ◇ y) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ y) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y))) ◇ x)) ◇ y) := by
    first | exact superpose ef217 ef20352 | exact superpose ef20352 ef217
  have ef21348 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (X0 ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y)) ◇
      ((x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ X0)))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (X0 ◇
      ((((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y)) ◇ ((x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ X0)))) ◇
      y) ◇ (X0 ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y)) ◇
      ((x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ X0)))) ◇ y) := by
    first | exact superpose ef31 ef20448 | exact superpose ef20448 ef31
  have ef21357 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (X0 ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y))) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ X0)))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      (X0 ◇
      ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y))) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ X0)))) ◇
      y) ◇ (X0 ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y))) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ X0)))) ◇ y) := by
    first | exact superpose ef217 ef21348 | exact superpose ef21348 ef217
  have ef21364 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)))) ◇ ((y ◇ (x ◇ x)) ◇
      (y ◇ (x ◇ x))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)))) ◇
      ((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))))) ◇ y) ◇ ((y ◇ (((y ◇ (x ◇ x)) ◇ y) ◇
      (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)))) ◇ ((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))))) ◇ y) := by
    first | exact superpose ef31 ef21357 | exact superpose ef21357 ef31
  have ef21367 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y))) ◇
      (y ◇ (x ◇ x))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y))) ◇ (y ◇ (x ◇ x))))) ◇ y) ◇ ((y ◇
      (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y))) ◇ (y ◇
      (x ◇ x))))) ◇ y) := by
    first | exact superpose ef217 ef21364 | exact superpose ef21364 ef217
  have ef21368 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ y) ◇
      ((x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ x))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ y) ◇ y) ◇ ((x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ x))))) ◇ y) ◇ ((y ◇
      (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ y) ◇ ((x ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇
      (x ◇ x))))) ◇ y) := by
    first | exact superpose ef217 ef21367 | exact superpose ef21367 ef217
  have ef21369 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ y) ◇
      ((x ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ x))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ y) ◇ y) ◇ ((x ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ x))))) ◇ y) ◇ ((y ◇
      (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ y) ◇ ((x ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ x))))) ◇ y) := by
    first | exact superpose ef217 ef21368 | exact superpose ef21368 ef217
  have ef21370 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ x)) ◇
      (y ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ x))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ x)) ◇ (y ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ x))))) ◇ y) ◇ ((y ◇
      (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ x)) ◇ (y ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ x))))) ◇ y) := by
    first | exact superpose ef217 ef21369 | exact superpose ef21369 ef217
  have ef21371 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ x)) ◇
      (y ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ x)) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      y) ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇ (x ◇ x)) ◇ (y ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef191 ef21370 | exact superpose ef21370 ef191
  have ef21372 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ (y ◇ x)) ◇
      (y ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ (y ◇ x)) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      y) ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ (y ◇ x)) ◇ (y ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef21371 | exact superpose ef21371 ef217
  have ef21373 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      y) ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef21372 | exact superpose ef21372 ef217
  have ef21374 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      (y ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) ◇ ((y ◇ (y ◇
      (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef21373 | exact superpose ef21373 ef217
  have ef21375 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((((((x ◇ x) ◇ x) ◇
      (y ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) ◇ ((y ◇ (y ◇
      (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef21374 | exact superpose ef21374 ef217
  have ef23206 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))) ◇
      ((y ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇ X0))) ◇ ((y ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef31 ef21375 | exact superpose ef21375 ef31
  have ef23237 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))) ◇
      ((y ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇ X0)) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23206 | exact superpose ef23206 ef217
  have ef23248 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (y ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0)) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23237 | exact superpose ef23237 ef217
  have ef23259 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (y ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))))) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ y)) ◇
      ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23248 | exact superpose ef23248 ef217
  have ef23263 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))))) ◇
      (((y ◇ (x ◇ x)) ◇ x) ◇ y)) ◇
      ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23259 | exact superpose ef23259 ef217
  have ef23266 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      y)) ◇ ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23263 | exact superpose ef23263 ef217
  have ef23269 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      y)) ◇ ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23266 | exact superpose ef23266 ef217
  have ef23272 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇
      y)) ◇ ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23269 | exact superpose ef23269 ef217
  have ef23273 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇
      y)) ◇ ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23272 | exact superpose ef23272 ef217
  have ef23274 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇
      y)) ◇ ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef191 ef23273 | exact superpose ef23273 ef191
  have ef23275 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇
      y)) ◇ ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23274 | exact superpose ef23274 ef217
  have ef23276 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇
      y)) ◇ ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23275 | exact superpose ef23275 ef217
  have ef23277 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇
      ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef30 ef23276 | exact superpose ef23276 ef30
  have ef23278 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((X0 ◇ (y ◇ (y ◇
      (x ◇ x)))) ◇ (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇
      ((((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ X0) ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23277 | exact superpose ef23277 ef217
  have ef23362 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ ((((((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ X0))) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇
      X0)) ◇ y) := by
    first | exact superpose ef89 ef23278 | exact superpose ef23278 ef89
  have ef23380 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ ((((((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇ y) ◇ ((((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ X0)) ◇ (y ◇ (x ◇ x)))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇
      X0)) ◇ y) := by
    first | exact superpose ef217 ef23362 | exact superpose ef23362 ef217
  have ef23436 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ ((((((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y))) ◇
      (((((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ X0)) ◇ (y ◇
      (x ◇ x))) ◇ X0)) ◇ y) := by
    first | exact superpose ef217 ef23380 | exact superpose ef23380 ef217
  have ef23480 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ ((((((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇ y) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      y) := by
    first | exact superpose ef191 ef23436 | exact superpose ef23436 ef191
  have ef23514 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ ((((((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇ y) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ y)) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇ ((y ◇
      (x ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef217 ef23480 | exact superpose ef23480 ef217
  have ef23539 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))))) ◇ (((y ◇ (x ◇ x)) ◇
      x) ◇ ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇ ((y ◇
      (x ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))) ◇ (((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇
      y))) := by
    first | exact superpose ef191 ef23514 | exact superpose ef23514 ef191
  have ef23550 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇ ((y ◇
      (x ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))) ◇ (((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇
      y))) := by
    first | exact superpose ef217 ef23539 | exact superpose ef23539 ef217
  have ef23559 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇ ((y ◇
      x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ (((y ◇ (x ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇
      y))) := by
    first | exact superpose ef217 ef23550 | exact superpose ef23550 ef217
  have ef23566 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y)) ◇ ((y ◇
      x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ y))) := by
    first | exact superpose ef31 ef23559 | exact superpose ef23559 ef31
  have ef23573 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      (((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ y))) := by
    first | exact superpose ef217 ef23566 | exact superpose ef23566 ef217
  have ef23579 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      ((((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ y) ◇
      ((x ◇ x) ◇ (y ◇ (x ◇ x)))) ◇ y))) := by
    first | exact superpose ef217 ef23573 | exact superpose ef23573 ef217
  have ef23584 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      ((((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇
      (x ◇ x)) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ y))) := by
    first | exact superpose ef217 ef23579 | exact superpose ef23579 ef217
  have ef23589 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      ((((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x)))) ◇ x)) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ y))) := by
    first | exact superpose ef217 ef23584 | exact superpose ef23584 ef217
  have ef23593 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      ((((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ y) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x)))) ◇ x) ◇ (y ◇ (x ◇ x)))) ◇ y))) := by
    first | exact superpose ef217 ef23589 | exact superpose ef23589 ef217
  have ef23597 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      ((((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ y) ◇ (x ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef191 ef23593 | exact superpose ef23593 ef191
  have ef23601 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      ((((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23597 | exact superpose ef23597 ef217
  have ef23604 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ (((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ y))) := by
    first | exact superpose ef217 ef23601 | exact superpose ef23601 ef217
  have ef23607 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ y)) ◇ ((y ◇ x) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ y))) := by
    first | exact superpose ef217 ef23604 | exact superpose ef23604 ef217
  have ef23609 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ y)) ◇ ((y ◇ x) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ y))) := by
    first | exact superpose ef217 ef23607 | exact superpose ef23607 ef217
  have ef23611 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ y))) := by
    first | exact superpose ef217 ef23609 | exact superpose ef23609 ef217
  have ef23612 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))))) ◇
      ((((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23611 | exact superpose ef23611 ef217
  have ef23613 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23612 | exact superpose ef23612 ef217
  have ef23614 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      (y ◇ x)) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x))) ◇ ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23613 | exact superpose ef23613 ef217
  have ef23615 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      y) ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x))) ◇ ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23614 | exact superpose ef23614 ef217
  have ef23616 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      y) ◇ (x ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23615 | exact superpose ef23615 ef217
  have ef23617 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (y ◇
      (y ◇ (x ◇ x))))) ◇
      (((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      x) ◇ (y ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23616 | exact superpose ef23616 ef217
  have ef23618 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      x) ◇ (y ◇ (y ◇ x)))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23617 | exact superpose ef23617 ef217
  have ef23619 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef191 ef23618 | exact superpose ef23618 ef191
  have ef23620 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef23619 | exact superpose ef23619 ef217
  have ef23627 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      (((((x ◇ x) ◇ x) ◇ X0) ◇ (X0 ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (y ◇
      (y ◇ x)))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef98 ef23620 | exact superpose ef23620 ef98
  have ef23912 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef30 ef23627 | exact superpose ef23627 ef30
  have ef24054 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ x) ◇ x)) ◇ (y ◇ (y ◇ x)))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇
      x))) ◇ ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef36 ef23912 | exact superpose ef23912 ef36
  have ef24083 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (y ◇ (y ◇ x)))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇
      x) ◇ x))) ◇ ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef24054 | exact superpose ef24054 ef217
  have ef24102 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef10 ef24083 | exact superpose ef24083 ef10
  have ef24150 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef98 ef24102 | exact superpose ef24102 ef98
  have ef24290 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (((y ◇ (x ◇ x)) ◇ x) ◇ y)) ◇
      (((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y)))) ◇ y))) := by
    first | exact superpose ef217 ef24150 | exact superpose ef24150 ef217
  have ef24324 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (((y ◇ (x ◇ x)) ◇ x) ◇ y)) ◇
      (((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x)))))) ◇ y))) := by
    first | exact superpose ef217 ef24290 | exact superpose ef24290 ef217
  have ef24354 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef191 ef24324 | exact superpose ef24324 ef191
  have ef24368 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24354 | exact superpose ef24354 ef217
  have ef24379 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      ((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24368 | exact superpose ef24368 ef217
  have ef24389 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y)))) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24379 | exact superpose ef24379 ef217
  have ef24399 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ y))) ◇
      x)) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24389 | exact superpose ef24389 ef217
  have ef24407 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x)))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef191 ef24399 | exact superpose ef24399 ef191
  have ef24412 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇
      ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇ ((y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x)))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24407 | exact superpose ef24407 ef217
  have ef24417 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇
      ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ X0) ◇ (X0 ◇ x)))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24412 | exact superpose ef24412 ef217
  have ef24422 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ X0) ◇ (X0 ◇ x)))))) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24417 | exact superpose ef24417 ef217
  have ef24427 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ X0) ◇ (X0 ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇
      (x ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ X0) ◇ (X0 ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇
      y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24422 | exact superpose ef24422 ef217
  have ef24480 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇
      (x ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ ((((x ◇ y) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ x))) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x))))) ◇ (((x ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef191 ef24427 | exact superpose ef24427 ef191
  have ef24567 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((x ◇ y) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef217 ef24480 | exact superpose ef24480 ef217
  have ef24604 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((x ◇ y) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24567 | exact superpose ef24567 ef217
  have ef24633 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((x ◇ y) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24604 | exact superpose ef24604 ef217
  have ef24659 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24633 | exact superpose ef24633 ef217
  have ef24677 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      ((((x ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ x))) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24659 | exact superpose ef24659 ef217
  have ef24689 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef96 ef24677 | exact superpose ef24677 ef96
  have ef24694 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((y ◇ (x ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24689 | exact superpose ef24689 ef217
  have ef24696 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇
      ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24694 | exact superpose ef24694 ef217
  have ef24698 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24696 | exact superpose ef24696 ef217
  have ef24699 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇
      (((y ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24698 | exact superpose ef24698 ef217
  have ef24700 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇
      (((y ◇ (x ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇
      (((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef217 ef24699 | exact superpose ef24699 ef217
  have ef24733 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇
      (((y ◇ (x ◇ x)) ◇ ((y ◇ X0) ◇ (X0 ◇ ((x ◇ x) ◇ x)))) ◇
      (((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)))))) := by
    first | exact superpose ef98 ef24700 | exact superpose ef24700 ef98
  have ef25151 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇
      ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (X0 ◇ (((y ◇ X1) ◇ (X1 ◇ ((x ◇ x) ◇ x))) ◇
      (((((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ X0)))))) := by
    first | exact superpose ef31 ef24733 | exact superpose ef24733 ef31
  have ef25158 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇
      ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (X0 ◇ (((y ◇ X1) ◇ (X1 ◇ ((x ◇ x) ◇ x))) ◇
      (((((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ y) ◇ ((((y ◇ y) ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (x ◇ x))) ◇ X0)))))) := by
    first | exact superpose ef217 ef25151 | exact superpose ef25151 ef217
  have ef25195 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇
      ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (X0 ◇ (((y ◇ X1) ◇ (X1 ◇ ((x ◇ x) ◇ x))) ◇
      (((((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ y) ◇ (y ◇ (x ◇ (y ◇ y)))) ◇ X0)))))) := by
    first | exact superpose ef191 ef25158 | exact superpose ef25158 ef191
  have ef25370 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇
      ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (y ◇ (X0 ◇
      (((((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ y) ◇ (y ◇ (x ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ x) ◇ X0))))))) := by
    first | exact superpose ef43 ef25195 | exact superpose ef25195 ef43
  have ef25382 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇ (X0 ◇
      (((((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ y) ◇ (y ◇ (x ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ x) ◇ X0))))))) := by
    first | exact superpose ef217 ef25370 | exact superpose ef25370 ef217
  have ef25430 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇ (X0 ◇
      (((((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ y) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ X0))))))) := by
    first | exact superpose ef217 ef25382 | exact superpose ef25382 ef217
  have ef25458 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇ (X0 ◇
      (((((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (x ◇ x)) ◇ (y ◇ x)) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ X0))))))) := by
    first | exact superpose ef217 ef25430 | exact superpose ef25430 ef217
  have ef25480 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (X0 ◇ (((x ◇ y) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ X0))))))) := by
    first | exact superpose ef191 ef25458 | exact superpose ef25458 ef191
  have ef25485 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))) ◇
      (X0 ◇ (((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ X0))))))) := by
    first | exact superpose ef217 ef25480 | exact superpose ef25480 ef217
  have ef25574 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ X0) ◇ (X0 ◇
      (((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef98 ef25485 | exact superpose ef25485 ef98
  have ef25582 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ X0) ◇ (X0 ◇
      (((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef217 ef25574 | exact superpose ef25574 ef217
  have ef25623 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ X0) ◇ (X0 ◇
      (((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ y)) ◇ ((x ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef217 ef25582 | exact superpose ef25582 ef217
  have ef25641 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ X0) ◇ (X0 ◇
      (((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef217 ef25623 | exact superpose ef25623 ef217
  have ef25653 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ X0) ◇ (X0 ◇
      (((x ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (x ◇ (x ◇ y))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef217 ef25641 | exact superpose ef25641 ef217
  have ef25656 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ X0) ◇ (X0 ◇
      (((x ◇ (x ◇ x)) ◇ (y ◇ (x ◇ (x ◇ y)))) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef217 ef25653 | exact superpose ef25653 ef217
  have ef25659 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ X0) ◇
      (X0 ◇ (x ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef29 ef25656 | exact superpose ef25656 ef29
  have ef25727 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ y))))) := by
    first | exact superpose ef31 ef25659 | exact superpose ef25659 ef31
  have ef25760 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x))) ◇ y))))) := by
    first | exact superpose ef217 ef25727 | exact superpose ef25727 ef217
  have ef25858 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ (X0 ◇ (y ◇
      (((((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x))) ◇ y)) ◇ ((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      X0))))) := by
    first | exact superpose ef31 ef25760 | exact superpose ef25760 ef31
  have ef25861 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ (X0 ◇ (y ◇
      (((((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x))) ◇ y) ◇ ((x ◇ x) ◇ x))) ◇
      X0))))) := by
    first | exact superpose ef217 ef25858 | exact superpose ef25858 ef217
  have ef25879 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ (X0 ◇ (y ◇
      (((((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x))) ◇ (x ◇ x)) ◇ (y ◇ x))) ◇
      X0))))) := by
    first | exact superpose ef217 ef25861 | exact superpose ef25861 ef217
  have ef25889 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((((x ◇ x) ◇ x) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇
      (y ◇ (y ◇ y))))) ◇ (X0 ◇ (y ◇
      (((((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ (y ◇ y)))) ◇
      X0))))) := by
    first | exact superpose ef191 ef25879 | exact superpose ef25879 ef191
  have ef25893 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      ((((y ◇ y) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ y) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef31 ef25889 | exact superpose ef25889 ef31
  have ef25894 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ y)) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef217 ef25893 | exact superpose ef25893 ef217
  have ef25895 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ y)) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ y) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef217 ef25894 | exact superpose ef25894 ef217
  have ef25896 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ y)) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (y ◇ ((y ◇ x) ◇ x))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef217 ef25895 | exact superpose ef25895 ef217
  have ef25897 :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (((((y ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (y ◇ ((y ◇ x) ◇ x))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef217 ef25896 | exact superpose ef25896 ef217
  have ef25917 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (((((y ◇ (x ◇ x)) ◇ X0) ◇ (X0 ◇ ((x ◇ x) ◇ x))) ◇ (y ◇ ((y ◇ x) ◇ x))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef98 ef25897 | exact superpose ef25897 ef98
  have ef26071 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (((((y ◇ (x ◇ x)) ◇ ((x ◇ X0) ◇ (X0 ◇ x))) ◇ x) ◇ (y ◇ ((y ◇ x) ◇ x))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef10 ef25917 | exact superpose ef25917 ef10
  have ef26126 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (((x ◇ (((x ◇ X0) ◇ (X0 ◇ x)) ◇ y)) ◇ (y ◇ ((y ◇ x) ◇ x))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef191 ef26071 | exact superpose ef26071 ef191
  have ef26165 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (((x ◇ y) ◇ ((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((y ◇ x) ◇ x))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef217 ef26126 | exact superpose ef26126 ef217
  have ef26383 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ (((x ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef217 ef26165 | exact superpose ef26165 ef217
  have ef26392 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((x ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef217 ef26383 | exact superpose ef26383 ef217
  have ef26417 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((x ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))))) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef217 ef26392 | exact superpose ef26392 ef217
  have ef26432 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) ◇
      (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((x ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))))) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef26417 | exact superpose ef26417 ef217
  have ef26443 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ ((x ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))))) ◇
      (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef26432 | exact superpose ef26432 ef217
  have ef26454 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇
      ((y ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))))) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef26443 | exact superpose ef26443 ef217
  have ef26463 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((y ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))))) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef26454 | exact superpose ef26454 ef217
  have ef27381 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ x))) ◇
      ((y ◇ X0) ◇ (X0 ◇ (y ◇ (y ◇ y)))))) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef98 ef26463 | exact superpose ef26463 ef98
  have ef27533 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇
      (X0 ◇ ((x ◇ x) ◇ (y ◇ (y ◇ y)))))) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef98 ef27381 | exact superpose ef27381 ef98
  have ef27913 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (((y ◇ (y ◇ y)) ◇ X0) ◇ (X0 ◇ x))) ◇
      x)) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef10 ef27533 | exact superpose ef27533 ef10
  have ef28031 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (((y ◇ (y ◇ y)) ◇ X0) ◇ (X0 ◇ x))) ◇
      x) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef27913 | exact superpose ef27913 ef217
  have ef28072 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((((y ◇ (y ◇ y)) ◇ X0) ◇ (X0 ◇ x)) ◇ ((x ◇ x) ◇ x))) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef191 ef28031 | exact superpose ef28031 ef191
  have ef28087 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (((((y ◇ (y ◇ y)) ◇ X0) ◇ (X0 ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef28072 | exact superpose ef28072 ef217
  have ef28170 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ (((((y ◇ (y ◇ y)) ◇ x) ◇ X0) ◇ (X0 ◇ x)) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef98 ef28087 | exact superpose ef28087 ef98
  have ef28320 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      (((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ (((y ◇ y) ◇ ((x ◇ y) ◇ x)) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef30 ef28170 | exact superpose ef28170 ef30
  have ef28436 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      ((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇
      ((y ◇ y) ◇ ((x ◇ y) ◇ x))) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef28320 | exact superpose ef28320 ef217
  have ef28452 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ y))) ◇
      (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ x)))) ◇
      (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef28436 | exact superpose ef28436 ef217
  have ef28461 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X0) ◇ (X0 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef217 ef28452 | exact superpose ef28452 ef217
  have ef28470 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      (((x ◇ X0) ◇ (X0 ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ x)))) ◇
      (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef98 ef28461 | exact superpose ef28461 ef98
  have ef28602 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      (((x ◇ y) ◇ X0) ◇ (X0 ◇ ((x ◇ y) ◇ x)))) ◇ (((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((((x ◇ X1) ◇ (X1 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef98 ef28470 | exact superpose ef28470 ef98
  have ef28860 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (((((x ◇ X2) ◇ (X2 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ X0))) := by
    first | exact superpose ef31 ef28602 | exact superpose ef28602 ef31
  have ef28863 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (((((x ◇ X2) ◇ (X2 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((x ◇ x) ◇ ((x ◇ x) ◇ x)))) ◇ X0))) := by
    first | exact superpose ef217 ef28860 | exact superpose ef28860 ef217
  have ef28912 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (x ◇ x)) ◇
      ((((((x ◇ X2) ◇ (X2 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28863 | exact superpose ef28863 ef217
  have ef28934 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (x ◇ x)) ◇
      ((((((x ◇ X2) ◇ (X2 ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇ (x ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28912 | exact superpose ef28912 ef217
  have ef28940 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (x ◇ x)) ◇
      ((((((x ◇ X2) ◇ (X2 ◇ x)) ◇ y) ◇ x) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28934 | exact superpose ef28934 ef217
  have ef28942 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (x ◇ x)) ◇
      (((X2 ◇ (y ◇ (x ◇ X2))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef191 ef28940 | exact superpose ef28940 ef191
  have ef28943 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((((y ◇ (x ◇ x)) ◇ (y ◇ (y ◇ y))) ◇ x) ◇ (y ◇ x)) ◇
      (((X2 ◇ (y ◇ (x ◇ X2))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28942 | exact superpose ef28942 ef217
  have ef28944 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((x ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (y ◇ x)) ◇
      (((X2 ◇ (y ◇ (x ◇ X2))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef191 ef28943 | exact superpose ef28943 ef191
  have ef28945 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇
      (((x ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x)) ◇
      (((X2 ◇ (y ◇ (x ◇ X2))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28944 | exact superpose ef28944 ef217
  have ef28946 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x)) ◇
      (((X2 ◇ (y ◇ (x ◇ X2))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28945 | exact superpose ef28945 ef217
  have ef28947 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((x ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X2 ◇ (y ◇ (x ◇ X2))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28946 | exact superpose ef28946 ef217
  have ef28948 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)) ◇
      ((x ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X2 ◇ (y ◇ (x ◇ X2))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28947 | exact superpose ef28947 ef217
  have ef28949 (X0 X1 X2 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (X0 ◇ ((((x ◇ y) ◇ X1) ◇ (X1 ◇ ((x ◇ y) ◇ x))) ◇
      (((((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ y)) ◇
      (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X2 ◇ (y ◇ (x ◇ X2))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      X0))) := by
    first | exact superpose ef217 ef28948 | exact superpose ef28948 ef217
  have ef29257 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ ((((x ◇ y) ◇ x) ◇ (((x ◇ y) ◇ X0) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ y)) ◇ (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))))) ◇
      X0) := by
    first | exact superpose ef29 ef28949 | exact superpose ef28949 ef29
  have ef29484 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ y) ◇ ((x ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ y)) ◇ (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X0 ◇ (y ◇ (x ◇ X0))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x))))) ◇ (x ◇
      y))) := by
    first | exact superpose ef42 ef29257 | exact superpose ef29257 ef42
  have ef29498 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ (x ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ y)) ◇ (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X0 ◇ (y ◇ (x ◇ X0))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x))))) ◇ (x ◇
      y))) := by
    first | exact superpose ef217 ef29484 | exact superpose ef29484 ef217
  have ef29535 (X0 : G) :
      x ≠ (((y ◇ y) ◇ y) ◇ (x ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      (((((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ y)) ◇
      (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X0 ◇ (y ◇ (x ◇ X0))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef217 ef29498 | exact superpose ef29498 ef217
  have ef29547 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      (((((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ y)) ◇
      (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X0 ◇ (y ◇ (x ◇ X0))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef217 ef29535 | exact superpose ef29535 ef217
  have ef29573 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      (((((((x ◇ x) ◇ x) ◇ X0) ◇ (X0 ◇ y)) ◇
      (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef98 ef29547 | exact superpose ef29547 ef98
  have ef29744 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((X0 ◇
      (((X0 ◇ (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ y) ◇ ((x ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef191 ef29573 | exact superpose ef29573 ef191
  have ef29823 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((X0 ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((X0 ◇ (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ y) ◇ ((x ◇ x) ◇ x)) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef217 ef29744 | exact superpose ef29744 ef217
  have ef29841 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((X0 ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((X0 ◇ (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x))) ◇ (x ◇ x)) ◇ (y ◇ x)) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef217 ef29823 | exact superpose ef29823 ef217
  have ef29851 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((X0 ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((X0 ◇ x) ◇ ((((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef217 ef29841 | exact superpose ef29841 ef217
  have ef29857 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((X0 ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((X0 ◇ x) ◇ y) ◇ (((((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x)) ◇ x) ◇ x)) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef217 ef29851 | exact superpose ef29851 ef217
  have ef29862 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((X0 ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((X0 ◇ x) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ (x ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)))) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef191 ef29857 | exact superpose ef29857 ef191
  have ef29866 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((X0 ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((X0 ◇ x) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)))) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef217 ef29862 | exact superpose ef29862 ef217
  have ef29991 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ ((X0 ◇
      ((((((x ◇ ((y ◇ x) ◇ x)) ◇ (X0 ◇ x)) ◇ x) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)))) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef42 ef29866 | exact superpose ef29866 ef42
  have ef30122 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ ((X0 ◇
      (((((y ◇ x) ◇ ((X0 ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)))) ◇
      (((X1 ◇ (y ◇ (x ◇ X1))) ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)))) ◇
      y))) := by
    first | exact superpose ef191 ef29991 | exact superpose ef29991 ef191
  have ef30255 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇ X0) ◇ (X0 ◇
      (y ◇ (x ◇ ((((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)))))))) ◇
      y))) := by
    first | exact superpose ef49 ef30122 | exact superpose ef30122 ef49
  have ef30391 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      ((((((x ◇ y) ◇ (y ◇ x)) ◇ x) ◇
      (((x ◇ ((((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x))))) ◇ X0) ◇ y)) ◇
      X0) ◇ y))) := by
    first | exact superpose ef30 ef30255 | exact superpose ef30255 ef30
  have ef30421 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇
      ((((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x))))) ◇
      X0) ◇ (X0 ◇ (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef191 ef30391 | exact superpose ef30391 ef191
  have ef30965 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (X0 ◇
      (((X0 ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)))) ◇
      (X1 ◇ (x ◇ ((((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ X1)))) ◇
      (((x ◇ y) ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef72 ef30421 | exact superpose ef30421 ef72
  have ef31086 (X0 X1 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (X0 ◇
      (((X0 ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)))) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇
      ((X1 ◇ (x ◇ ((((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ X1))) ◇ x))))) := by
    first | exact superpose ef217 ef30965 | exact superpose ef30965 ef217
  have ef31156 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (X0 ◇
      (((X0 ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)))) ◇ ((x ◇ y) ◇ (y ◇ x))) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef31 ef31086 | exact superpose ef31086 ef31
  have ef31174 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (X0 ◇
      (((X0 ◇ (x ◇ y)) ◇ ((((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x))) ◇ (y ◇ x))) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef217 ef31156 | exact superpose ef31156 ef217
  have ef31186 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (X0 ◇
      (((X0 ◇ (x ◇ y)) ◇ ((((y ◇ (y ◇ y)) ◇ x) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)) ◇ x))) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef217 ef31174 | exact superpose ef31174 ef217
  have ef31198 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (X0 ◇
      (((X0 ◇ (x ◇ y)) ◇ ((y ◇ (x ◇ y)) ◇ ((y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)) ◇ x))) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef191 ef31186 | exact superpose ef31186 ef191
  have ef31368 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      ((((y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)) ◇ x) ◇ x) ◇ ((X0 ◇ ((y ◇ (x ◇ y)) ◇ (y ◇ X0))) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef55 ef31198 | exact superpose ef31198 ef55
  have ef31413 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      ((((y ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ x)) ◇ x) ◇ x) ◇ ((X0 ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ X0))) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef217 ef31368 | exact superpose ef31368 ef217
  have ef31428 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ (y ◇ (x ◇ x))) ◇
      (x ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ X0))) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef191 ef31413 | exact superpose ef31413 ef191
  have ef31438 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ X0))) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef217 ef31428 | exact superpose ef31428 ef217
  have ef31484 :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇
      (((y ◇ x) ◇ ((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇ x))))) := by
    first | exact superpose ef8 ef31438 | exact superpose ef31438 ef8
  have ef31586 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇
      (X0 ◇ (((y ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ X0))))))) := by
    first | exact superpose ef31 ef31484 | exact superpose ef31484 ef31
  have ef31589 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇
      (X0 ◇ (((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ (((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ X0))))))) := by
    first | exact superpose ef217 ef31586 | exact superpose ef31586 ef217
  have ef31597 :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇
      ((x ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef31 ef31589 | exact superpose ef31589 ef31
  have ef31626 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇
      ((x ◇ ((y ◇ X0) ◇ (X0 ◇ (y ◇ x)))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef98 ef31597 | exact superpose ef31597 ef98
  have ef31897 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇
      ((x ◇ ((y ◇ ((x ◇ X0) ◇ y)) ◇ X0)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef30 ef31626 | exact superpose ef31626 ef30
  have ef32689 :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      (((y ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y)) ◇
      (((y ◇ (y ◇ y)) ◇ x) ◇ (y ◇ ((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y)))))) := by
    first | exact superpose ef11 ef31897 | exact superpose ef31897 ef11
  have ef32733 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ X0))) ◇
      (y ◇ ((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y)))))) := by
    first | exact superpose ef31 ef32689 | exact superpose ef32689 ef31
  have ef32758 (X0 : G) :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (((y ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ y)) ◇ ((X0 ◇ y) ◇
      (((y ◇ y) ◇ ((x ◇ y) ◇ X0)) ◇ ((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y)))))) := by
    first | exact superpose ef217 ef32733 | exact superpose ef32733 ef217
  have ef35518 :
      x ≠ (((y ◇ y) ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      (((y ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y)) ◇
      (((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))) ◇ y) ◇ y)))) := by
    first | exact superpose ef40 ef32758 | exact superpose ef32758 ef40
  have ef35554 (X0 : G) :
      x ≠ ((X0 ◇ (y ◇ ((x ◇ y) ◇ X0))) ◇ (y ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      (((y ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y)) ◇
      (((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))) ◇ y) ◇ y)))) := by
    first | exact superpose ef31 ef35518 | exact superpose ef35518 ef31
  have ef35607 (X0 : G) :
      x ≠ ((X0 ◇ y) ◇ ((y ◇ ((x ◇ y) ◇ X0)) ◇ y)) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇
      (((y ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y)) ◇
      (((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))) ◇ y) ◇ y)))) := by
    first | exact superpose ef217 ef35554 | exact superpose ef35554 ef217
  have ef35614 (X0 : G) :
      x ≠ ((X0 ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ ((x ◇ y) ◇ X0)) ◇ y) ◇ ((x ◇ x) ◇
      (((y ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y)) ◇
      (((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))) ◇ y) ◇ y)))) := by
    first | exact superpose ef217 ef35607 | exact superpose ef35607 ef217
  have ef35618 (X0 : G) :
      x ≠ ((X0 ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ ((x ◇ y) ◇ X0)) ◇ (x ◇ x)) ◇ (y ◇
      (((y ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y)) ◇
      (((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))) ◇ y) ◇ y)))) := by
    first | exact superpose ef217 ef35614 | exact superpose ef35614 ef217
  have ef35621 (X0 : G) :
      x ≠ ((X0 ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ ((x ◇ y) ◇ X0)) ◇ (x ◇ x)) ◇
      ((y ◇ ((y ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y))) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))))) := by
    first | exact superpose ef31 ef35618 | exact superpose ef35618 ef31
  have ef35624 (X0 : G) :
      x ≠ ((X0 ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ ((x ◇ y) ◇ X0)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))))) := by
    first | exact superpose ef31 ef35621 | exact superpose ef35621 ef31
  have ef35627 (X0 : G) :
      x ≠ ((X0 ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ x) ◇ (((x ◇ y) ◇ X0) ◇ x)) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))))) := by
    first | exact superpose ef217 ef35624 | exact superpose ef35624 ef217
  have ef35630 (X0 : G) :
      x ≠ ((X0 ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇
      ((((x ◇ y) ◇ X0) ◇ x) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))))) := by
    first | exact superpose ef217 ef35627 | exact superpose ef35627 ef217
  have ef35631 (X0 : G) :
      x ≠ ((X0 ◇ y) ◇ ((y ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y))) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ y) ◇ X0) ◇ x) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))))) := by
    first | exact superpose ef217 ef35630 | exact superpose ef35630 ef217
  have ef35643 (X0 : G) :
      x ≠ y ◇ (((y ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇ (X0 ◇ (y ◇ (x ◇ X0))))) ◇ x) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))))) := by
    first | exact superpose ef77 ef35631 | exact superpose ef35631 ef77
  have ef35811 (X0 X1 : G) :
      x ≠ y ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ (X0 ◇ (x ◇
      (((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (y ◇ (x ◇ y))) ◇
      ((x ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇ (X1 ◇ (y ◇ (x ◇ X1)))))) ◇ X0)))) := by
    first | exact superpose ef31 ef35643 | exact superpose ef35643 ef31
  have ef35814 (X0 X1 : G) :
      x ≠ y ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ (X0 ◇ (x ◇
      (((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (x ◇ y)) ◇
      ((y ◇ (x ◇ y)) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇ (X1 ◇ (y ◇ (x ◇ X1)))))) ◇ X0)))) := by
    first | exact superpose ef217 ef35811 | exact superpose ef35811 ef217
  have ef35823 (X0 : G) :
      x ≠ y ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ (X0 ◇ (x ◇
      (((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (x ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇
      X0)))) := by
    first | exact superpose ef72 ef35814 | exact superpose ef35814 ef72
  have ef35828 :
      x ≠ y ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (x ◇ y)))) := by
    first | exact superpose ef31 ef35823 | exact superpose ef35823 ef31
  have ef35829 :
      x ≠ y ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ x) ◇ (y ◇ y)))) := by
    first | exact superpose ef217 ef35828 | exact superpose ef35828 ef217
  have ef35832 (X0 : G) :
      x ≠ y ◇ ((X0 ◇ ((x ◇ x) ◇ ((x ◇ y) ◇ X0))) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇
      (((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ x) ◇ (y ◇ y)))) := by
    first | exact superpose ef31 ef35829 | exact superpose ef35829 ef31
  have ef35934 (X0 : G) :
      x ≠ y ◇ (X0 ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇
      (((x ◇ y) ◇ ((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ x) ◇ (y ◇ y)) ◇ (x ◇ x))) ◇
      X0))) := by
    first | exact superpose ef55 ef35832 | exact superpose ef35832 ef55
  have ef35941 (X0 : G) :
      x ≠ y ◇ (X0 ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇
      (((x ◇ y) ◇ ((((x ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ x) ◇ x) ◇ ((y ◇ y) ◇ x))) ◇
      X0))) := by
    first | exact superpose ef217 ef35934 | exact superpose ef35934 ef217
  have ef35960 (X0 : G) :
      x ≠ y ◇ (X0 ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇
      (((x ◇ y) ◇ (((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ x))) ◇ X0))) := by
    first | exact superpose ef191 ef35941 | exact superpose ef35941 ef191
  have ef36159 :
      x ≠ y ◇ (((((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ y)) := by
    first | exact superpose ef30 ef35960 | exact superpose ef35960 ef30
  have ef36223 :
      x ≠ y ◇ ((x ◇ (((y ◇ y) ◇ x) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ y)) := by
    first | exact superpose ef191 ef36159 | exact superpose ef36159 ef191
  have ef36239 :
      x ≠ y ◇ ((x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ x) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ y)) := by
    first | exact superpose ef217 ef36223 | exact superpose ef36223 ef217
  have ef36270 (X0 : G) :
      x ≠ X0 ◇ ((x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ x) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ X0)) := by
    first | exact superpose ef33 ef36239 | exact superpose ef36239 ef33
  have ef36297 (X0 : G) :
      x ≠ (X0 ◇ (x ◇ (((y ◇ y) ◇ x) ◇ X0))) ◇
      ((x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef29 ef36270 | exact superpose ef36270 ef29
  have ef36362 (X0 : G) :
      x ≠ (X0 ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇
      ((x ◇ (((y ◇ y) ◇ x) ◇ X0)) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef217 ef36297 | exact superpose ef36297 ef217
  have ef36372 (X0 : G) :
      x ≠ (X0 ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇
      ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ x) ◇ X0) ◇ x)) := by
    first | exact superpose ef217 ef36362 | exact superpose ef36362 ef217
  have ef36491 (X0 X1 : G) :
      x ≠ ((x ◇ ((X1 ◇ (y ◇ y)) ◇ X0)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇
      ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((X0 ◇ X1) ◇ x)) := by
    first | exact superpose ef36 ef36372 | exact superpose ef36372 ef36
  have ef36538 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ (((X1 ◇ (y ◇ y)) ◇ X0) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇
      ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((X0 ◇ X1) ◇ x)) := by
    first | exact superpose ef217 ef36491 | exact superpose ef36491 ef217
  have ef36562 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ (x ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((X1 ◇ (y ◇ y)) ◇ X0) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ ((X0 ◇ X1) ◇ x)) := by
    first | exact superpose ef217 ef36538 | exact superpose ef36538 ef217
  have ef36582 (X0 X1 : G) :
      x ≠ (x ◇ (y ◇ x)) ◇
      ((((X1 ◇ (y ◇ y)) ◇ X0) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ ((X0 ◇ X1) ◇ x)) := by
    first | exact superpose ef36 ef36562 | exact superpose ef36562 ef36
  have ef37609 : x ≠ (x ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ x)) := by
    first | exact superpose ef30 ef36582 | exact superpose ef36582 ef30
  have ef37718 : x ≠ (x ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ (y ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef191 ef37609 | exact superpose ef37609 ef191
  have ef37764 (X0 : G) : x ≠ (x ◇ (y ◇ x)) ◇ ((y ◇ X0) ◇ (X0 ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef98 ef37718 | exact superpose ef37718 ef98
  have ef38490 : x ≠ x := by
    first | exact superpose ef35 ef37764 | exact superpose ef37764 ef35
  exact absurd rfl ef38490

theorem Equation667_termDefinableFrom_Equation898 : Law667.TermDefinableFrom Law898 := by
  intro G M hGL
  have h : Equation898 G := Law898.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op (M.op x y) (M.op x x)) (M.op x y)) (M.op y x))⟩, ?_, ?_⟩
  · rw [@Law667.models_iff]
    exact fun x y ↦ @aux898_667 G M h _ (fun _ _ ↦ rfl) x y
  · exact ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 0) (Term.var 1))) (tm (Term.var 1) (Term.var 0))), rfl⟩

set_option maxHeartbeats 1200000 in
/-- Equation 917 `x = y ◇ ((y ◇ y) ◇ (x ◇ y))` holds of the operation
`x □ y := (((x*x)*(y*(y*x)))*(y*(x*x)))` in every magma satisfying equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. -/
private theorem aux898_917 [Magma G] (h : Equation898 G) (wf : G → G → G)
    (hwdef : ∀ a b : G, wf a b = ((a ◇ a) ◇ (b ◇ (b ◇ a))) ◇ (b ◇ (a ◇ a))) (x y : G) :
    x = wf y (wf (wf y y) (wf x y)) := by
  by_contra nh
  have ef6 : x ≠ wf y (wf (wf y y) (wf x y)) := mod_symm nh
  have ef7 (X0 X1 : G) :
      wf X0 X1 = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ X0)) := mod_symm (hwdef ..)
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0) = X3 := by
    first | exact superpose ef8 ef8
  have ef11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0 = X2 := by
    first | exact superpose ef8 ef8
  have ef15 :
      x ≠ ((y ◇ y) ◇ ((wf (wf y y) (wf x y)) ◇ ((wf (wf y y) (wf x y)) ◇ y))) ◇
      ((wf (wf y y) (wf x y)) ◇ (y ◇ y)) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef16 :
      x ≠ ((y ◇ y) ◇ (((((wf y y) ◇ (wf y y)) ◇ ((wf x y) ◇ ((wf x y) ◇ (wf y y)))) ◇ ((wf x y) ◇
      ((wf y y) ◇ (wf y y)))) ◇ (((((wf y y) ◇ (wf y y)) ◇ ((wf x y) ◇ ((wf x y) ◇ (wf y y)))) ◇
      ((wf x y) ◇ ((wf y y) ◇ (wf y y)))) ◇ y))) ◇ (((((wf y y) ◇ (wf y y)) ◇ ((wf x y) ◇
      ((wf x y) ◇ (wf y y)))) ◇ ((wf x y) ◇ ((wf y y) ◇ (wf y y)))) ◇ (y ◇ y)) := by
    first | exact superpose ef7 ef15 | exact superpose ef15 ef7
  have ef20 :
      x ≠ ((y ◇ y) ◇ (((((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))) ◇ ((wf x y) ◇
      ((wf x y) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇ ((wf x y) ◇
      ((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇
      (((((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))) ◇
      ((wf x y) ◇ ((wf x y) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇ ((wf x y) ◇
      ((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇
      y))) ◇ (((((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇
      (y ◇ (y ◇ y)))) ◇ ((wf x y) ◇ ((wf x y) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇
      ((wf x y) ◇ ((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇
      (y ◇ (y ◇ y)))))) ◇ (y ◇ y)) := by
    first | exact superpose ef7 ef16 | exact superpose ef16 ef7
  have ef24 :
      x ≠ ((y ◇ y) ◇ (((((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇
      (((((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇
      y))) ◇ (((((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇
      (y ◇ (y ◇ y)))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y)))))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇
      (x ◇ x))) ◇ ((((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇
      (y ◇ (y ◇ y)))))) ◇ (y ◇ y)) := by
    first | exact superpose ef7 ef20 | exact superpose ef20 ef7
  have ef29 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X2 := by
    first | exact superpose ef11 ef11
  have ef30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1) = X2 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef31 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2)) = (X1 ◇ X0) ◇ X3 := by
    first | exact superpose ef11 ef11
  have ef33 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ (X3 ◇ X2)) = X1 ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef36 (X0 X1 X2 X3 : G) : X2 ◇ X1 = (X0 ◇ X3) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2)) := by
    first | exact superpose ef30 ef30
  have ef41 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef30 ef30
  have ef42 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef30 ef11 | exact superpose ef11 ef30
  have ef43 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef30 ef8 | exact superpose ef8 ef30
  have ef77 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X0) ◇ ((X4 ◇ X3) ◇ X1) = X4 := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef96 (X0 X1 X2 X3 : G) : X2 ◇ X3 = X0 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef10 ef30 | exact superpose ef30 ef10
  have ef98 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X2 ◇ X3) = (X1 ◇ X0) ◇ (X0 ◇ X3) := by
    first | exact superpose ef10 ef11 | exact superpose ef11 ef10
  have ef191 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3 := by
    first | exact superpose ef29 ef11 | exact superpose ef11 ef29
  have ef217 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef30 ef31 | exact superpose ef31 ef30
  have ef5516 :
      x ≠ ((y ◇ y) ◇ (((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      (((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      y))) ◇ (((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇
      (x ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ (y ◇ y)) := by
    first | exact superpose ef217 ef24 | exact superpose ef24 ef217
  have ef5766 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇
      (x ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y))))))) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      (((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      y)) ◇ (y ◇ y)) := by
    first | exact superpose ef217 ef5516 | exact superpose ef5516 ef217
  have ef6165 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇
      (x ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y))))))) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef5766 | exact superpose ef5766 ef217
  have ef6542 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))))) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))))))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef6165 | exact superpose ef6165 ef217
  have ef6914 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))))))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef6542 | exact superpose ef6542 ef217
  have ef7286 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))))))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef6914 | exact superpose ef6914 ef217
  have ef7658 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ (y ◇ y))))))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ (y ◇ y)))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef7286 | exact superpose ef7286 ef217
  have ef8030 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ y)))))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ y))))) ◇ y) ◇
      y)) := by
    first | exact superpose ef10 ef7658 | exact superpose ef7658 ef10
  have ef8402 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ y)))))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ y))))) ◇ y) ◇
      y)) := by
    first | exact superpose ef217 ef8030 | exact superpose ef8030 ef217
  have ef8774 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ y))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ (y ◇ (y ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef30 ef8402 | exact superpose ef8402 ef30
  have ef9146 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x))) ◇ y) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x))) ◇ y) ◇ y))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ x))) ◇ y) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef8774 | exact superpose ef8774 ef217
  have ef9518 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ y))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef9146 | exact superpose ef9146 ef217
  have ef9890 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ y))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y)))) ◇
      (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef9518 | exact superpose ef9518 ef217
  have ef10260 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇
      (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef9890 | exact superpose ef9890 ef217
  have ef10630 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef10260 | exact superpose ef10260 ef217
  have ef11000 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef10630 | exact superpose ef10630 ef217
  have ef11369 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ x) ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ x) ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇
      y))) ◇ y) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ x) ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef11000 | exact superpose ef11000 ef217
  have ef11732 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ x) ◇ x)) ◇ y)))) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ x) ◇ x)) ◇
      y))) ◇ y) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ x) ◇ x)) ◇ y))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef11369 | exact superpose ef11369 ef217
  have ef12079 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇ ((y ◇ y) ◇
      (((y ◇ x) ◇ x) ◇ (y ◇ y)))))) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇
      ((x ◇ x) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇ ((y ◇ y) ◇ (((y ◇ x) ◇ x) ◇ (y ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y)))) ◇
      ((y ◇ y) ◇ (((y ◇ x) ◇ x) ◇ (y ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef191 ef11732 | exact superpose ef11732 ef191
  have ef12412 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇
      (((y ◇ x) ◇ x) ◇ (y ◇ y)))))) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇
      ((x ◇ x) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (((y ◇ x) ◇ x) ◇ (y ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (((y ◇ x) ◇ x) ◇ (y ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef12079 | exact superpose ef12079 ef217
  have ef12733 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ y)))))) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇
      ((x ◇ x) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef12412 | exact superpose ef12412 ef217
  have ef13035 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇
      ((x ◇ x) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ (y ◇ x)) ◇ (y ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef12733 | exact superpose ef12733 ef217
  have ef13328 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇
      ((x ◇ x) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef13035 | exact superpose ef13035 ef217
  have ef13601 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef13328 | exact superpose ef13328 ef217
  have ef13865 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef13601 | exact superpose ef13601 ef217
  have ef14126 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef13865 | exact superpose ef13865 ef217
  have ef14382 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((((((y ◇ y) ◇ x) ◇ (y ◇ x)) ◇
      (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef14126 | exact superpose ef14126 ef217
  have ef14636 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ x) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((((((y ◇ y) ◇ x) ◇ ((x ◇ x) ◇ y)) ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      ((((((((y ◇ y) ◇ x) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef14382 | exact superpose ef14382 ef217
  have ef20917 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ (((x ◇ x) ◇ y) ◇
      ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇
      ((y ◇ x) ◇ y))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇
      (((x ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      (((((X0 ◇ (((x ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef31 ef14636 | exact superpose ef14636 ef31
  have ef20957 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇
      ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0)) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇
      (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0)) ◇
      ((y ◇ x) ◇ y))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0)) ◇ ((y ◇ x) ◇ y))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef20917 | exact superpose ef20917 ef217
  have ef20970 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((x ◇ x) ◇ y) ◇
      ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0)) ◇ ((y ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇
      (((y ◇ y) ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((x ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0)) ◇
      ((y ◇ x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((x ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0)) ◇ ((y ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef20957 | exact superpose ef20957 ef217
  have ef20979 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇
      (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇ (((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ y)) := by
    first | exact superpose ef217 ef20970 | exact superpose ef20970 ef217
  have ef20988 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x))) ◇
      ((((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x))) ◇
      ((((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x))) ◇
      ((((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef20979 | exact superpose ef20979 ef217
  have ef20995 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((y ◇ y) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef20988 | exact superpose ef20988 ef217
  have ef21002 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ (((((X0 ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((x ◇ x) ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef20995 | exact superpose ef20995 ef217
  have ef21006 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ (((x ◇ x) ◇ y) ◇ (y ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇ (((x ◇ x) ◇ y) ◇ (y ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ (((((X0 ◇ (((x ◇ x) ◇ y) ◇ (y ◇ x))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef21002 | exact superpose ef21002 ef217
  have ef21010 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((X0 ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ (((((X0 ◇ x) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef30 ef21006 | exact superpose ef21006 ef30
  have ef21030 (X0 : G) :
      x ≠ ((y ◇ y) ◇ ((X0 ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((X0 ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ ((((X0 ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x)) ◇ (y ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef33 ef21010 | exact superpose ef21010 ef33
  have ef21120 (X0 : G) :
      x ≠ ((y ◇ y) ◇ ((X0 ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((X0 ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ ((((X0 ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef217 ef21030 | exact superpose ef21030 ef217
  have ef21132 (X0 : G) :
      x ≠ ((y ◇ y) ◇ ((X0 ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ ((((X0 ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ ((((X0 ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ X0))) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef191 ef21120 | exact superpose ef21120 ef191
  have ef21147 :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ y) ◇ (((((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      y) ◇ y)) := by
    first | exact superpose ef30 ef21132 | exact superpose ef21132 ef30
  have ef21258 :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇ (y ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇
      (y ◇ y))) ◇ y)) := by
    first | exact superpose ef191 ef21147 | exact superpose ef21147 ef191
  have ef21273 :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      y))) ◇ y)) := by
    first | exact superpose ef217 ef21258 | exact superpose ef21258 ef217
  have ef21332 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇
      (((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      (((X0 ◇ (((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      (((X0 ◇ (((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      y))) ◇ y)) := by
    first | exact superpose ef31 ef21273 | exact superpose ef21273 ef31
  have ef21353 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0)) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇ (((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      y))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      (((X0 ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      y))) ◇ y)) := by
    first | exact superpose ef217 ef21332 | exact superpose ef21332 ef217
  have ef21367 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0)) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇ ((y ◇ y) ◇
      (((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      X0)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇
      (((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ X0)))) ◇
      y)) := by
    first | exact superpose ef191 ef21353 | exact superpose ef21353 ef191
  have ef21377 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0)) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇ ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      y)) := by
    first | exact superpose ef191 ef21367 | exact superpose ef21367 ef191
  have ef21383 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇
      (((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0) ◇ y)))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      y)) := by
    first | exact superpose ef217 ef21377 | exact superpose ef21377 ef217
  have ef21384 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ (X0 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇ ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      y)) := by
    first | exact superpose ef191 ef21383 | exact superpose ef21383 ef191
  have ef21385 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ x) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X0 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇ ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      y)) := by
    first | exact superpose ef217 ef21384 | exact superpose ef21384 ef217
  have ef21386 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X0 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇ ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      y)) := by
    first | exact superpose ef217 ef21385 | exact superpose ef21385 ef217
  have ef21387 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X0 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇ ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      y)) := by
    first | exact superpose ef217 ef21386 | exact superpose ef21386 ef217
  have ef21388 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X0 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X0 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇ ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ y) ◇
      ((y ◇ y) ◇
      ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))))) ◇
      y)) := by
    first | exact superpose ef217 ef21387 | exact superpose ef21387 ef217
  have ef21465 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X1 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X1 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      ((((y ◇ y) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      X0)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      ((((y ◇ y) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))))) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ X0)))) ◇
      y)) := by
    first | exact superpose ef31 ef21388 | exact superpose ef21388 ef31
  have ef21478 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X1 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X1 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇ (((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x))))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      X0)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇ (((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x))))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ X0)))) ◇
      y)) := by
    first | exact superpose ef217 ef21465 | exact superpose ef21465 ef217
  have ef21504 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X1 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X1 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇ (((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇
      X0)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇ (((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇ X0)))) ◇
      y)) := by
    first | exact superpose ef217 ef21478 | exact superpose ef21478 ef217
  have ef21523 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X1 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X1 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇
      X0)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇ X0)))) ◇
      y)) := by
    first | exact superpose ef217 ef21504 | exact superpose ef21504 ef217
  have ef21538 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ ((X1 ◇ ((y ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (X1 ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇
      X0)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X0 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇ X0)))) ◇
      y)) := by
    first | exact superpose ef43 ef21523 | exact superpose ef21523 ef43
  have ef21572 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ (y ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇
      X1)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇ X1)))) ◇
      y)) := by
    first | exact superpose ef10 ef21538 | exact superpose ef21538 ef10
  have ef21731 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      y) ◇ (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇
      X1)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇ X1)))) ◇
      y)) := by
    first | exact superpose ef217 ef21572 | exact superpose ef21572 ef217
  have ef21760 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇
      X1)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇ X1)))) ◇
      y)) := by
    first | exact superpose ef191 ef21731 | exact superpose ef21731 ef191
  have ef21773 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇
      X1)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇ X1)))) ◇
      y)) := by
    first | exact superpose ef217 ef21760 | exact superpose ef21760 ef217
  have ef21781 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (y ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇
      X1)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (X1 ◇ (y ◇
      (((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y))) ◇ X1)))) ◇
      y)) := by
    first | exact superpose ef8 ef21773 | exact superpose ef21773 ef8
  have ef21853 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (y ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇
      ((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇ (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇
      ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      (((y ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇ (y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇ y)) := by
    first | exact superpose ef42 ef21781 | exact superpose ef21781 ef42
  have ef22022 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((((y ◇ x) ◇ (x ◇ y)) ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y)))) ◇ (((y ◇ y) ◇
      y) ◇ y)) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      (((y ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇ (y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇
      (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇
      y)) := by
    first | exact superpose ef36 ef21853 | exact superpose ef21853 ef36
  have ef22078 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇
      (((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      (((y ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇ (y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇
      (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇
      y)) := by
    first | exact superpose ef217 ef22022 | exact superpose ef22022 ef217
  have ef22166 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇
      (((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y))) ◇ y)) ◇ (((X0 ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇
      (((y ◇ (((X0 ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇ (y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇ (((X0 ◇
      (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇
      (((y ◇ (((X0 ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇
      (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇
      y)) := by
    first | exact superpose ef31 ef22078 | exact superpose ef22078 ef31
  have ef22216 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇
      (((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y))) ◇ y)) ◇ (((X0 ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇
      (((y ◇ (((X0 ◇ (y ◇ x)) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ X0)) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇ (y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇ (((X0 ◇
      (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇
      (((y ◇ (((X0 ◇ (y ◇ x)) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ X0)) ◇ (x ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇
      (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇
      y)) := by
    first | exact superpose ef217 ef22166 | exact superpose ef22166 ef217
  have ef22236 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇
      (((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y))) ◇ y)) ◇ (((X0 ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇
      (((y ◇ (((X0 ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ X0) ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇ (y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇ (((X0 ◇
      (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇
      (((y ◇ (((X0 ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ X0) ◇ (y ◇ x)))) ◇ y)) ◇ y) ◇
      (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇
      y)) := by
    first | exact superpose ef217 ef22216 | exact superpose ef22216 ef217
  have ef22246 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇
      (((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y))) ◇ y)) ◇ (((X0 ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇
      (((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇ (((X0 ◇
      (y ◇ ((y ◇ (y ◇ y)) ◇ X0))) ◇ (((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇
      (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇
      y)) := by
    first | exact superpose ef36 ef22236 | exact superpose ef22236 ef36
  have ef22611 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((((y ◇ x) ◇
      (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇
      (((((y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇
      ((y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) ◇
      (((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇
      ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ ((y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (y ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) := by
    first | exact superpose ef41 ef22246 | exact superpose ef22246 ef41
  have ef22620 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((((y ◇ x) ◇
      (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇
      (((((y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇
      ((y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) ◇
      y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇
      ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))))) ◇ ((y ◇ (y ◇ y)) ◇ ((y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (y ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) := by
    first | exact superpose ef217 ef22611 | exact superpose ef22611 ef217
  have ef22657 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((((y ◇ x) ◇
      (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇
      (((((y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇
      ((y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) ◇
      y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ ((y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (y ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) := by
    first | exact superpose ef217 ef22620 | exact superpose ef22620 ef217
  have ef22680 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((((y ◇ x) ◇
      (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇
      (((((y ◇ y) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇
      ((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) ◇
      y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ ((y ◇ y) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) := by
    first | exact superpose ef217 ef22657 | exact superpose ef22657 ef217
  have ef22692 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((((y ◇ x) ◇
      (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇
      (((((y ◇ y) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇
      ((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) ◇
      y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ y)) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)))))) := by
    first | exact superpose ef217 ef22680 | exact superpose ef22680 ef217
  have ef22702 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((((y ◇ x) ◇
      (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇
      (((((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇
      ((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))))) ◇
      y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ y)) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))))) := by
    first | exact superpose ef217 ef22692 | exact superpose ef22692 ef217
  have ef22710 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((((y ◇ x) ◇
      (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇
      (((((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇
      ((y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))))) ◇
      y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ y)) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))))) := by
    first | exact superpose ef217 ef22702 | exact superpose ef22702 ef217
  have ef22715 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (((((y ◇ x) ◇
      (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y)) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇
      ((y ◇ (y ◇ y)) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))))) := by
    first | exact superpose ef31 ef22710 | exact superpose ef22710 ef31
  have ef22718 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ (y ◇ (y ◇
      y))) ◇ ((y ◇ (y ◇ y)) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇
      ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))))) := by
    first | exact superpose ef217 ef22715 | exact superpose ef22715 ef217
  have ef22794 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ X0) ◇
      (X0 ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))))) := by
    first | exact superpose ef98 ef22718 | exact superpose ef22718 ef98
  have ef22958 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      X1) ◇ (X1 ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))))) ◇ (y ◇ ((x ◇ x) ◇ y)))) := by
    first | exact superpose ef10 ef22794 | exact superpose ef22794 ef10
  have ef22985 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ y) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      X1) ◇ (X1 ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))))) ◇ ((x ◇ x) ◇ y)))) := by
    first | exact superpose ef217 ef22958 | exact superpose ef22958 ef217
  have ef23023 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ (((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ y) ◇ y) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      X1) ◇ (x ◇ x)) ◇ ((X1 ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ y)))) := by
    first | exact superpose ef217 ef22985 | exact superpose ef22985 ef217
  have ef23051 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ (y ◇ (y ◇ y))) ◇ (y ◇ y)) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      X1) ◇ (x ◇ x)) ◇ ((X1 ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ y)))) := by
    first | exact superpose ef191 ef23023 | exact superpose ef23023 ef191
  have ef23061 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      X1) ◇ (x ◇ x)) ◇ ((X1 ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y))))) ◇ y)))) := by
    first | exact superpose ef217 ef23051 | exact superpose ef23051 ef217
  have ef24681 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      (y ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ y) ◇ y)))) := by
    first | exact superpose ef31 ef23061 | exact superpose ef23061 ef31
  have ef24741 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      x) ◇ ((y ◇ (y ◇ y)) ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ y) ◇ y)))) := by
    first | exact superpose ef217 ef24681 | exact superpose ef24681 ef217
  have ef24805 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ y)) ◇ (((y ◇ (y ◇ y)) ◇ x) ◇ y)))) := by
    first | exact superpose ef217 ef24741 | exact superpose ef24741 ef217
  have ef24843 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ y)) ◇ (y ◇ (x ◇ y))))) := by
    first | exact superpose ef191 ef24805 | exact superpose ef24805 ef191
  have ef24869 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      x) ◇ y) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ y) ◇ (x ◇ y))))) := by
    first | exact superpose ef217 ef24843 | exact superpose ef24843 ef217
  have ef24877 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      x) ◇ y) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ (y ◇ y))))) := by
    first | exact superpose ef217 ef24869 | exact superpose ef24869 ef217
  have ef24881 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      (x ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ (y ◇ y))))) := by
    first | exact superpose ef191 ef24877 | exact superpose ef24877 ef191
  have ef24884 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇
      ((x ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ (y ◇ y))))) := by
    first | exact superpose ef217 ef24881 | exact superpose ef24881 ef217
  have ef24887 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇
      ((x ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) := by
    first | exact superpose ef217 ef24884 | exact superpose ef24884 ef217
  have ef24890 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ (x ◇ y)) ◇
      (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) := by
    first | exact superpose ef217 ef24887 | exact superpose ef24887 ef217
  have ef24891 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y)) ◇
      (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) := by
    first | exact superpose ef217 ef24890 | exact superpose ef24890 ef217
  have ef24892 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ x) ◇ (x ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇
      ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) := by
    first | exact superpose ef217 ef24891 | exact superpose ef24891 ef217
  have ef24902 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((((y ◇ X0) ◇ (X0 ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇
      ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) := by
    first | exact superpose ef98 ef24892 | exact superpose ef24892 ef98
  have ef25370 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((X0 ◇ (((X0 ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇
      (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y))) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇
      ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) := by
    first | exact superpose ef191 ef24902 | exact superpose ef24902 ef191
  have ef25468 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((X0 ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ y) ◇ ((((y ◇ y) ◇ y) ◇
      (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y)) ◇ X0)) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇
      ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) := by
    first | exact superpose ef191 ef25370 | exact superpose ef25370 ef191
  have ef25507 (X0 X1 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ ((((X0 ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ y) ◇ (((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇
      (((((y ◇ y) ◇ y) ◇ (((y ◇ X1) ◇ (X1 ◇ y)) ◇ y)) ◇ X0) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇
      ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇
      (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) := by
    first | exact superpose ef217 ef25468 | exact superpose ef25468 ef217
  have ef25786 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇
      ((((((y ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))) ◇
      (y ◇ y)) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y))) ◇ y) ◇ (((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇ (((y ◇
      X0) ◇ (X0 ◇ y)) ◇ y)) := by
    first | exact superpose ef41 ef25507 | exact superpose ef25507 ef41
  have ef25794 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ y)) ◇ (y ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))))) ◇
      (((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y)) := by
    first | exact superpose ef191 ef25786 | exact superpose ef25786 ef191
  have ef25851 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ y)) ◇ (y ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))))) ◇
      ((y ◇ (y ◇ y)) ◇ y))) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y)) := by
    first | exact superpose ef217 ef25794 | exact superpose ef25794 ef217
  have ef25894 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((y ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))) ◇
      y))) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y)) := by
    first | exact superpose ef217 ef25851 | exact superpose ef25851 ef217
  have ef25906 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ y) ◇ (((y ◇ x) ◇ y) ◇ (y ◇ y))) ◇ ((y ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))) ◇
      y))) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y)) := by
    first | exact superpose ef217 ef25894 | exact superpose ef25894 ef217
  have ef25913 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))) ◇
      y))) ◇ (((y ◇ X0) ◇ (X0 ◇ y)) ◇ y)) := by
    first | exact superpose ef30 ef25906 | exact superpose ef25906 ef30
  have ef25993 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))) ◇
      y))) ◇ (X0 ◇ (((X0 ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef191 ef25913 | exact superpose ef25913 ef191
  have ef26107 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ X0) ◇ (X0 ◇
      (((((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))) ◇ y)) ◇
      y) ◇ y) ◇ y))) := by
    first | exact superpose ef98 ef25993 | exact superpose ef25993 ef98
  have ef26114 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ X0) ◇ (X0 ◇ (((y ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)))) ◇
      (y ◇ (((y ◇ x) ◇ y) ◇ x))) ◇ y))) := by
    first | exact superpose ef191 ef26107 | exact superpose ef26107 ef191
  have ef26134 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ X0) ◇ (X0 ◇ (((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y))) ◇
      (((y ◇ x) ◇ y) ◇ x))) ◇ y))) := by
    first | exact superpose ef217 ef26114 | exact superpose ef26114 ef217
  have ef26148 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ X0) ◇ (X0 ◇ (((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ ((y ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x))) ◇
      y))) := by
    first | exact superpose ef217 ef26134 | exact superpose ef26134 ef217
  have ef26153 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ X0) ◇ (X0 ◇ (((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x))) ◇
      y))) := by
    first | exact superpose ef217 ef26148 | exact superpose ef26148 ef217
  have ef26232 (X0 : G) :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (((y ◇ ((y ◇ x) ◇ y)) ◇ ((y ◇ X0) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x))))) ◇
      X0) := by
    first | exact superpose ef30 ef26153 | exact superpose ef26153 ef30
  have ef26387 :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇
      y) ◇ y)) ◇ (y ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef42 ef26232 | exact superpose ef26232 ef42
  have ef26402 :
      x ≠ ((((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ (((((y ◇ y) ◇
      y) ◇ y) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef217 ef26387 | exact superpose ef26387 ef217
  have ef26463 (X0 : G) :
      x ≠ (((X0 ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ X0))) ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef31 ef26402 | exact superpose ef26402 ef31
  have ef26532 (X0 : G) :
      x ≠ (((X0 ◇ (y ◇ y)) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ X0)) ◇ y)) ◇ y) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef217 ef26463 | exact superpose ef26463 ef217
  have ef26543 (X0 : G) :
      x ≠ (y ◇ (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ X0)) ◇ y) ◇ X0)) ◇ (((((y ◇
      y) ◇ y) ◇ y) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef191 ef26532 | exact superpose ef26532 ef191
  have ef26549 (X0 : G) :
      x ≠ (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ ((((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇
      X0)) ◇ y) ◇ X0) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef217 ef26543 | exact superpose ef26543 ef217
  have ef26551 :
      x ≠ (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ ((y ◇ x) ◇ ((y ◇ x) ◇
      x)))) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef191 ef26549 | exact superpose ef26549 ef191
  have ef26552 :
      x ≠ (y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef217 ef26551 | exact superpose ef26551 ef217
  have ef26553 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef217 ef26552 | exact superpose ef26552 ef217
  have ef26589 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ (X0 ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ X0)))) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef31 ef26553 | exact superpose ef26553 ef31
  have ef28441 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ ((x ◇ ((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)))) ◇ (y ◇ x))) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef29 ef26589 | exact superpose ef26589 ef29
  have ef28475 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ ((x ◇ y) ◇ (((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))) ◇ x))) ◇ x)))) ◇
      y)) := by
    first | exact superpose ef217 ef28441 | exact superpose ef28441 ef217
  have ef28544 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (X0 ◇ (((x ◇ y) ◇ (((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))) ◇ x)) ◇ ((x ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y)) ◇ X0)))))) ◇
      y)) := by
    first | exact superpose ef31 ef28475 | exact superpose ef28475 ef31
  have ef28551 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      (X0 ◇ (((x ◇ y) ◇ (x ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))) ◇ ((((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))) ◇ x) ◇ X0)))))) ◇
      y)) := by
    first | exact superpose ef217 ef28544 | exact superpose ef28544 ef217
  have ef28570 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y)) ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y)))) ◇ ((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))))))) ◇
      y)) := by
    first | exact superpose ef31 ef28551 | exact superpose ef28551 ef31
  have ef28581 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ (y ◇ x)) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))) ◇
      ((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))))))) ◇
      y)) := by
    first | exact superpose ef217 ef28570 | exact superpose ef28570 ef217
  have ef28586 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (x ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))) ◇
      ((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))))))) ◇
      y)) := by
    first | exact superpose ef217 ef28581 | exact superpose ef28581 ef217
  have ef28588 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))) ◇
      ((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))))))) ◇
      y)) := by
    first | exact superpose ef217 ef28586 | exact superpose ef28586 ef217
  have ef28793 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ (X0 ◇ (((y ◇ y) ◇
      (((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))) ◇
      ((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)))))) ◇
      ((y ◇ ((y ◇ x) ◇ y)) ◇ X0)))) := by
    first | exact superpose ef31 ef28588 | exact superpose ef28588 ef31
  have ef28796 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ (X0 ◇ (((y ◇ y) ◇ (y ◇ ((y ◇ x) ◇ y))) ◇
      ((((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))) ◇
      ((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))))) ◇
      X0)))) := by
    first | exact superpose ef217 ef28793 | exact superpose ef28793 ef217
  have ef28810 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)))) ◇
      ((y ◇ y) ◇ (y ◇ ((y ◇ x) ◇ y)))) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef31 ef28796 | exact superpose ef28796 ef31
  have ef28823 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ (y ◇ y)) ◇
      (((y ◇ x) ◇ (y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y))) ◇ (y ◇ ((y ◇ x) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef28810 | exact superpose ef28810 ef217
  have ef28835 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ (y ◇ y)) ◇
      (((y ◇ x) ◇ y) ◇ ((y ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇ ((y ◇ x) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef28823 | exact superpose ef28823 ef217
  have ef28842 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ (y ◇ y)) ◇
      (((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef28835 | exact superpose ef28835 ef217
  have ef28846 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ (y ◇ y)) ◇
      (((y ◇ x) ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ (y ◇ (y ◇ (y ◇ x)))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef191 ef28842 | exact superpose ef28842 ef191
  have ef28850 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ y) ◇ (y ◇ y)) ◇
      (((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef28846 | exact superpose ef28846 ef217
  have ef28875 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ X0) ◇ (X0 ◇ y)) ◇
      (((y ◇ x) ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef98 ef28850 | exact superpose ef28850 ef98
  have ef29000 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((((((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ (y ◇ x)) ◇ X0) ◇
      (X0 ◇ ((y ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))))) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef98 ef28875 | exact superpose ef28875 ef98
  have ef29780 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((y ◇ x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ ((y ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef30 ef29000 | exact superpose ef29000 ef30
  have ef29902 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef29780 | exact superpose ef29780 ef217
  have ef29939 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ (y ◇ x)) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ (y ◇ x)))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef29902 | exact superpose ef29902 ef217
  have ef29970 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ y) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ (y ◇ x)))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef29939 | exact superpose ef29939 ef217
  have ef29984 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ (y ◇ x)))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef29970 | exact superpose ef29970 ef217
  have ef29992 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ x)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef30 ef29984 | exact superpose ef29984 ef30
  have ef30006 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((y ◇ X0) ◇ (X0 ◇ (y ◇ x))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ x)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef98 ef29992 | exact superpose ef29992 ef98
  have ef30157 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (X0 ◇ (((X0 ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ x))) ◇ (y ◇ x)) ◇ y))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef191 ef30006 | exact superpose ef30006 ef191
  have ef30193 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (X0 ◇ (((X0 ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ x)) ◇ y))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef30157 | exact superpose ef30157 ef217
  have ef31736 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      ((X0 ◇ (((X0 ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ x)) ◇ y)) ◇
      ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef30193 | exact superpose ef30193 ef217
  have ef31740 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇ ((X0 ◇ (y ◇ x)) ◇
      ((((X0 ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ x)) ◇ y) ◇
      ((x ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef31736 | exact superpose ef31736 ef217
  have ef31756 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇ ((X0 ◇ (y ◇ x)) ◇
      ((((X0 ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ x)) ◇ (x ◇ x)) ◇
      (y ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef31740 | exact superpose ef31740 ef217
  have ef31767 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇ ((X0 ◇ (y ◇ x)) ◇
      ((((X0 ◇ y) ◇ x) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ x) ◇ x)) ◇
      (y ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef31756 | exact superpose ef31756 ef217
  have ef31777 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇ ((X0 ◇ (y ◇ x)) ◇ ((((X0 ◇ y) ◇ x) ◇ y) ◇
      (((((y ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ x) ◇ x) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef31767 | exact superpose ef31767 ef217
  have ef31782 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇ ((X0 ◇ (y ◇ x)) ◇ ((((X0 ◇ y) ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef191 ef31777 | exact superpose ef31777 ef191
  have ef31787 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇ ((X0 ◇ (y ◇ x)) ◇ ((((X0 ◇ y) ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef31782 | exact superpose ef31782 ef217
  have ef31909 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((x ◇ (X0 ◇ (y ◇ x))) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ ((((X0 ◇ y) ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef217 ef31787 | exact superpose ef31787 ef217
  have ef33366 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ (X0 ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ (((((X0 ◇ y) ◇ y) ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))))))) := by
    first | exact superpose ef8 ef31909 | exact superpose ef31909 ef8
  have ef33496 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      ((((((y ◇ y) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y))) ◇ y) ◇ y) ◇ x))) := by
    first | exact superpose ef31 ef33366 | exact superpose ef33366 ef31
  have ef33550 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      (((X0 ◇ (((x ◇ (y ◇ y)) ◇ (((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ X0))) ◇
      y) ◇ x))) := by
    first | exact superpose ef31 ef33496 | exact superpose ef33496 ef31
  have ef33559 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      (((X0 ◇ (((x ◇ (y ◇ y)) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ ((((y ◇ x) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ X0))) ◇
      y) ◇ x))) := by
    first | exact superpose ef217 ef33550 | exact superpose ef33550 ef217
  have ef33564 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y) ◇ x))) := by
    first | exact superpose ef31 ef33559 | exact superpose ef33559 ef31
  have ef33566 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33564 | exact superpose ef33564 ef217
  have ef33567 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((y ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ y)) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ ((y ◇ x) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33566 | exact superpose ef33566 ef217
  have ef33568 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((y ◇ (y ◇ x)) ◇ (((x ◇ (y ◇ y)) ◇ (y ◇ x)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33567 | exact superpose ef33567 ef217
  have ef33569 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((y ◇ (y ◇ x)) ◇ (((x ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x))) ◇ y)) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33568 | exact superpose ef33568 ef217
  have ef33628 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (X0 ◇
      ((((x ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x)) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ X0)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef31 ef33569 | exact superpose ef33569 ef31
  have ef33647 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (X0 ◇
      ((((x ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ (y ◇ (y ◇ x)))) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ x) ◇ X0)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33628 | exact superpose ef33628 ef217
  have ef33648 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ ((x ◇ (((x ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ (y ◇ (y ◇ x))))) ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef31 ef33647 | exact superpose ef33647 ef31
  have ef33649 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ ((x ◇ y) ◇ ((((x ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ (y ◇ (y ◇ x)))) ◇ ((y ◇ y) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33648 | exact superpose ef33648 ef217
  have ef33650 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ ((x ◇ y) ◇ ((((x ◇ y) ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ y)) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33649 | exact superpose ef33649 ef217
  have ef33651 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ ((x ◇ y) ◇ ((((x ◇ y) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33650 | exact superpose ef33650 ef217
  have ef33652 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ ((x ◇ y) ◇ ((((x ◇ y) ◇ y) ◇ (y ◇ (y ◇ (y ◇ x)))) ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef33651 | exact superpose ef33651 ef217
  have ef33664 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇
      ((y ◇ ((x ◇ y) ◇ ((((x ◇ y) ◇ X0) ◇ (X0 ◇ (y ◇ (y ◇ x)))) ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ y)))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef98 ef33652 | exact superpose ef33652 ef98
  have ef33763 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇
      ((y ◇ ((x ◇ y) ◇ (X0 ◇ (((X0 ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ y)) ◇ (y ◇ (y ◇ x))) ◇ (x ◇ y))))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef191 ef33664 | exact superpose ef33664 ef191
  have ef33789 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      (((x ◇ y) ◇ (X0 ◇ (((X0 ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ y)) ◇ (y ◇ (y ◇ x))) ◇ (x ◇ y)))) ◇
      x))) := by
    first | exact superpose ef217 ef33763 | exact superpose ef33763 ef217
  have ef33816 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ (y ◇ x)) ◇ X0) ◇ (X0 ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ y))) ◇ x))) := by
    first | exact superpose ef31 ef33789 | exact superpose ef33789 ef31
  have ef33900 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ (y ◇ x)) ◇ ((y ◇ X0) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ X0) ◇ x))) := by
    first | exact superpose ef30 ef33816 | exact superpose ef33816 ef30
  have ef35680 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x)) ◇
      ((y ◇ (((y ◇ x) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ x) ◇ y)))) := by
    first | exact superpose ef41 ef33900 | exact superpose ef33900 ef41
  have ef35691 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇ (((((y ◇ y) ◇ y) ◇ y) ◇
      y) ◇ ((y ◇ (y ◇ (((y ◇ x) ◇ x) ◇ y))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) := by
    first | exact superpose ef217 ef35680 | exact superpose ef35680 ef217
  have ef35711 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (((x ◇ y) ◇ (y ◇ x)) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) := by
    first | exact superpose ef31 ef35691 | exact superpose ef35691 ef31
  have ef35731 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (((x ◇ X0) ◇ (X0 ◇ x)) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) := by
    first | exact superpose ef98 ef35711 | exact superpose ef35711 ef98
  have ef35826 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (((x ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x)) ◇ X0) ◇ (X0 ◇ (((y ◇ y) ◇ x) ◇ y)))) := by
    first | exact superpose ef98 ef35731 | exact superpose ef35731 ef98
  have ef35906 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (((x ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x)) ◇ ((y ◇ X0) ◇ ((y ◇ y) ◇ x))) ◇ X0)) := by
    first | exact superpose ef30 ef35826 | exact superpose ef35826 ef30
  have ef36098 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (y ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef43 ef35906 | exact superpose ef35906 ef43
  have ef36180 (X0 : G) :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ X0) ◇
      (X0 ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef98 ef36098 | exact superpose ef36098 ef98
  have ef37137 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))))) ◇
      (y ◇ ((y ◇ (y ◇ y)) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef30 ef36180 | exact superpose ef36180 ef30
  have ef37224 :
      x ≠ (y ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((y ◇ (y ◇ y)) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef217 ef37137 | exact superpose ef37137 ef217
  have ef37228 :
      x ≠ (y ◇ y) ◇ (((y ◇ y) ◇ (y ◇ (y ◇ y))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef217 ef37224 | exact superpose ef37224 ef217
  have ef37229 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ X0) ◇ (X0 ◇ (y ◇ y))) ◇ ((((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇
      ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef98 ef37228 | exact superpose ef37228 ef98
  have ef37316 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ X0) ◇ (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((X0 ◇ (y ◇ y)) ◇ ((((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef217 ef37229 | exact superpose ef37229 ef217
  have ef37661 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ (x ◇ (X0 ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ X0))))) ◇
      (((x ◇ x) ◇ y) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x)) := by
    first | exact superpose ef77 ef37316 | exact superpose ef37316 ef77
  have ef37675 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇
      ((x ◇ (X0 ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ X0)))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x)))) ◇
      ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ x)) := by
    first | exact superpose ef217 ef37661 | exact superpose ef37661 ef217
  have ef37713 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇
      (((x ◇ (X0 ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ X0)))) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ x))) ◇ x)) := by
    first | exact superpose ef217 ef37675 | exact superpose ef37675 ef217
  have ef37727 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇
      (((x ◇ (y ◇ x)) ◇ ((X0 ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ X0))) ◇ ((y ◇ x) ◇ x))) ◇ x)) := by
    first | exact superpose ef217 ef37713 | exact superpose ef37713 ef217
  have ef37736 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ (((y ◇ x) ◇ (y ◇ y)) ◇ y)) ◇
      (y ◇ (((X0 ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ X0))) ◇ ((y ◇ x) ◇ x)) ◇ x))) := by
    first | exact superpose ef191 ef37727 | exact superpose ef37727 ef191
  have ef37743 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇
      (((X0 ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ X0))) ◇ ((y ◇ x) ◇ x)) ◇ x))) := by
    first | exact superpose ef217 ef37736 | exact superpose ef37736 ef217
  have ef37746 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇
      (((X0 ◇ (y ◇ x)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ X0)) ◇ x)) ◇ x))) := by
    first | exact superpose ef217 ef37743 | exact superpose ef37743 ef217
  have ef37748 (X0 : G) :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ (y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ X0)) ◇ x) ◇ X0)))) := by
    first | exact superpose ef191 ef37746 | exact superpose ef37746 ef191
  have ef37749 :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (((y ◇ y) ◇ x) ◇ (x ◇ (y ◇ y)))))) := by
    first | exact superpose ef191 ef37748 | exact superpose ef37748 ef191
  have ef37750 :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ y) ◇ y))) := by
    first | exact superpose ef96 ef37749 | exact superpose ef37749 ef96
  have ef37755 (X0 : G) :
      x ≠ (y ◇ y) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ ((X0 ◇ ((y ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ X0))) ◇ ((y ◇ y) ◇ y))) := by
    first | exact superpose ef31 ef37750 | exact superpose ef37750 ef31
  have ef37762 (X0 : G) :
      x ≠ (y ◇ y) ◇
      (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ ((X0 ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ ((y ◇ (y ◇ x)) ◇ X0)) ◇ y))) := by
    first | exact superpose ef217 ef37755 | exact superpose ef37755 ef217
  have ef37984 :
      x ≠ (y ◇ y) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ ((((y ◇ x) ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ (y ◇ y))) := by
    first | exact superpose ef8 ef37762 | exact superpose ef37762 ef8
  have ef38008 : x ≠ ((y ◇ y) ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ y)) ◇ ((y ◇ x) ◇ (y ◇ y)) := by
    first | exact superpose ef31 ef37984 | exact superpose ef37984 ef31
  have ef38028 : x ≠ ((y ◇ y) ◇ (y ◇ x)) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (y ◇ y)) := by
    first | exact superpose ef217 ef38008 | exact superpose ef38008 ef217
  have ef38035 : x ≠ ((y ◇ y) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ y) := by
    first | exact superpose ef30 ef38028 | exact superpose ef38028 ef30
  subsumption ef38035 ef10

theorem Equation917_termDefinableFrom_Equation898 : Law917.TermDefinableFrom Law898 := by
  intro G M hGL
  have h : Equation898 G := Law898.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) (M.op y (M.op y x))) (M.op y (M.op x x)))⟩, ?_, ?_⟩
  · rw [@Law917.models_iff]
    exact fun x y ↦ @aux898_917 G M h _ (fun _ _ ↦ rfl) x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))) (tm (Term.var 1) (tm (Term.var 0) (Term.var 0)))), rfl⟩

end Law.MagmaLaw
