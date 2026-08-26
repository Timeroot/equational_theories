import equational_theories.Definability.FiniteFlavour
import equational_theories.Equations.All
import equational_theories.Superposition
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Term-structural facts witnessed by a term and its inverse

`Law.MagmaLaw.TermStructuralFrom t s` asks for more than `TermDefinableFrom t s`: the new
operation must carry all of the information of the old one, so the old one has to be a term of the
new one as well. A uniform witness is therefore a *pair* of binary terms -- `w` with
`s ⊢ t[◇ := w]`, and `v` with `s ⊢ v[□ := w] = x ◇ y`.

The pairs below come from the binary clone of a product of small models of the source law: every
member of that clone is a candidate `w`, and `v` is found by enumerating the short terms in `w`
alone and asking which of them reproduces the operation table. Both obligations are then replayed
from a Vampire refutation, in the style of `Generated/VampireProven`.

The inverse obligation does not mention the target, so one `inv` lemma serves every target that
its term reaches. Lemmas named `Fin` need a finite carrier: their replay uses the cyclic rotations
of the source law, which hold because a surjective self-map of a finite set is injective.
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

/-- On a finite carrier a one-sided inverse is two-sided: this is what turns a source law into its
cyclic rotations. -/
private theorem rot_of_finite [Finite G] {f g : G → G} (hfg : ∀ z, f (g z) = z) (x : G) :
    g (f x) = x := by
  have hs : Function.Surjective f := fun z ↦ ⟨g z, hfg z⟩
  exact Finite.injective_iff_surjective.mpr hs (hfg (f x))

/-!
The witnesses in this file are *parastrophes*: `w` is the left division `x : y`, defined by
`x ◇ (x : y) = y`, or the right division `x / y`, defined by `(x / y) ◇ y = x`, of the source law's
operation. When that division is itself a term in `◇` the pair `(w, v)` is immediate, because a
division is its own kind of inverse -- `◇` is recovered as a division of `:`.

The ETP commentary calls the resulting relation between two laws *parastrophic equivalence*, and
records dozens of instances of it in prose. The terms here were rediscovered by searching short
terms against finite models of each source law and then proving both obligations with Vampire, so
they are not always the term the prose names; where a cell also appears in
`Definability/PositiveStructural.lean` the two witnesses are different terms.
-/

/-- The defining term `x □ y := x ◇ ((y ◇ (x ◇ y)) ◇ y)` of equation 65 `x = y ◇ (x ◇ (y ◇ x))` can
be undone: the operation is recovered as `x ◇ y = x ◇ ((y ◇ (x ◇ y)) ◇ y)` read in `□` over a
finite carrier. -/
private theorem inv65_73f9f1faf [Finite G] [Magma G] (h : Equation65 G) (x y : G) :
    x ◇ ((((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ ((y ◇
      ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇
      y)) ◇ (x ◇ ((y ◇
      (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      ((y ◇ ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇
      y)))) ◇ ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇
      ((y ◇ (x ◇ y)) ◇ y)))) ◇ ((y ◇
      ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      y)) ◇ y))) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ◇ y ≠ x ◇ ((((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ ((y ◇
      ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇
      y)) ◇ (x ◇ ((y ◇
      (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      ((y ◇ ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇
      y)))) ◇ ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇
      ((y ◇ (x ◇ y)) ◇ y)))) ◇ ((y ◇
      ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      y)) ◇ y))) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose ef6 ef6
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef22 (X0 X1 : G) : X1 ◇ X0 = (X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    first | exact superpose ef10 ef7 | exact superpose ef7 ef10
  have ef44 :
      x ◇ y ≠ x ◇ (((((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇ y)) ◇ (x ◇
      (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇ y)))) ◇ (((x ◇
      ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ ((y ◇
      (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇ y))) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef45 :
      x ◇ y ≠ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇ y)) ◇ (x ◇
      (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇
      ((y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇ y))) := by
    first | exact superpose ef9 ef44 | exact superpose ef44 ef9
  have ef53 :
      x ◇ y ≠ (y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y)) ◇
      (x ◇ (y ◇ (((x ◇ ((y ◇ (x ◇ y)) ◇ y)) ◇ (y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y)))) ◇ y))) := by
    first | exact superpose ef9 ef45 | exact superpose ef45 ef9
  have ef59 :
      x ◇ y ≠ (y ◇ (((y ◇ (x ◇ y)) ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y)) ◇
      (x ◇ (y ◇ (((y ◇ (x ◇ y)) ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y))) := by
    first | exact superpose ef9 ef53 | exact superpose ef53 ef9
  have ef63 : x ◇ y ≠ (y ◇ ((x ◇ y) ◇ y)) ◇ (x ◇ (y ◇ ((x ◇ y) ◇ y))) := by
    first | exact superpose ef7 ef59 | exact superpose ef59 ef7
  subsumption ef63 ef22

/-- Equation 359 `x ◇ x = (x ◇ x) ◇ x` holds of the term `x □ y := x ◇ ((y ◇ (x ◇ y)) ◇ y)` over any
finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_359 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x ◇ ((x ◇ (x ◇ x)) ◇ x) = (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ◇ ((x ◇ (x ◇ x)) ◇ x) ≠ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose ef6 ef6
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef13 : x ◇ (x ◇ x) ≠ (x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef17 : x ◇ (x ◇ x) ≠ x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef9 ef13 | exact superpose ef13 ef9
  subsumption ef17 ef9

theorem Equation359_termStructuralFromFin_Equation65_parastrophic :
    Law359.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op y (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law359.models_iff]
    exact fun x ↦ @aux65_359 G _ M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), funext fun z ↦ (@inv65_73f9f1faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 614 `x = x ◇ (x ◇ ((x ◇ x) ◇ x))` holds of the term `x □ y := x ◇ ((y ◇ (x ◇ y)) ◇ y)`
over any finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_614 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x = x ◇ (((x ◇ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))) ◇ (x ◇ (x ◇
      ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))))) ◇ (x ◇
      ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))) ◇ ((x ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ x ◇ (((x ◇ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))) ◇ (x ◇ (x ◇
      ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))))) ◇ (x ◇
      ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)))) ◇ ((x ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x))))) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose ef6 ef6
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef17 :
      x ≠ x ◇ (((x ◇ ((((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))) ◇ ((x ◇ (x ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))) ◇ (x ◇ (x ◇
      ((((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))))) ◇ (x ◇ ((((x ◇ (x ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x))))) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef18 :
      x ≠ (x ◇ ((((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))) ◇ ((x ◇ (x ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))) ◇ (x ◇ (x ◇
      ((((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))) ◇ ((x ◇ (x ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x))))) := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  have ef20 :
      x ≠ (((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)))) ◇ ((x ◇ (x ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) := by
    first | exact superpose ef7 ef18 | exact superpose ef18 ef7
  have ef22 :
      x ≠ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef9 ef20 | exact superpose ef20 ef9
  have ef24 : x ≠ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef9 ef22 | exact superpose ef22 ef9
  have ef26 : x ≠ (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef7 ef24 | exact superpose ef24 ef7
  subsumption ef26 ef7

theorem Equation614_termStructuralFromFin_Equation65_parastrophic :
    Law614.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op y (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law614.models_iff]
    exact fun x ↦ @aux65_614 G _ M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), funext fun z ↦ (@inv65_73f9f1faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 817 `x = x ◇ ((x ◇ x) ◇ (x ◇ x))` holds of the term `x □ y := x ◇ ((y ◇ (x ◇ y)) ◇ y)`
over any finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_817 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x = x ◇ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ x ◇ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇
      x))))) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose ef6 ef6
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef17 :
      x ≠ x ◇
      ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))))) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef18 :
      x ≠ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  have ef20 :
      x ≠ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef9 ef18 | exact superpose ef18 ef9
  have ef22 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef14 ef20 | exact superpose ef20 ef14
  have ef24 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef9 ef22 | exact superpose ef22 ef9
  have ef26 : x ≠ (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef11 ef24 | exact superpose ef24 ef11
  subsumption ef26 ef7

theorem Equation817_termStructuralFromFin_Equation65_parastrophic :
    Law817.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op y (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law817.models_iff]
    exact fun x ↦ @aux65_817 G _ M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), funext fun z ↦ (@inv65_73f9f1faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1426 `x = (x ◇ x) ◇ (x ◇ (x ◇ x))` holds of the term `x □ y := x ◇ ((y ◇ (x ◇ y)) ◇ y)`
over any finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_1426 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x = (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))))) ◇ (x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))))) ◇ (x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose ef6 ef6
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef17 :
      x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x)))))) ◇ (x ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef18 :
      x ≠ (x ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  have ef20 :
      x ≠ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef9 ef18 | exact superpose ef18 ef9
  have ef22 : x ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef7 ef20 | exact superpose ef20 ef7
  subsumption ef22 ef6

theorem Equation1426_termStructuralFromFin_Equation65_parastrophic :
    Law1426.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op y (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law1426.models_iff]
    exact fun x ↦ @aux65_1426 G _ M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), funext fun z ↦ (@inv65_73f9f1faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1491 `x = (y ◇ x) ◇ (y ◇ (y ◇ x))` holds of the term `x □ y := x ◇ ((y ◇ (x ◇ y)) ◇ y)`
over any finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_1491 [Finite G] [Magma G] (h : Equation65 G) (x y : G) :
    x = (y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (((y ◇ (((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      (y ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇ ((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      (y ◇ (((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇
      (y ◇ ((x ◇ (y ◇ x)) ◇ x)))))) ◇ (y ◇ (((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (y ◇
      (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ (y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (((y ◇ (((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      (y ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇ ((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇
      (y ◇ (((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (y ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇
      (y ◇ ((x ◇ (y ◇ x)) ◇ x)))))) ◇ (y ◇ (((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (y ◇
      (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x))))) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose ef6 ef6
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef16 :
      x ≠ (y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (((y ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇
      ((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (y ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))))) ◇ (y ◇
      (((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef17 :
      x ≠ (y ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)))) ◇
      ((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ (y ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x))))) := by
    first | exact superpose ef9 ef16 | exact superpose ef16 ef9
  have ef18 : x ≠ ((x ◇ (y ◇ x)) ◇ x) ◇ ((y ◇ ((x ◇ (y ◇ x)) ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ x)) := by
    first | exact superpose ef6 ef17 | exact superpose ef17 ef6
  have ef19 : x ≠ y ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ x)) := by
    first | exact superpose ef10 ef18 | exact superpose ef18 ef10
  have ef20 : x ≠ y ◇ (x ◇ (y ◇ x)) := by
    first | exact superpose ef9 ef19 | exact superpose ef19 ef9
  subsumption ef20 ef6

theorem Equation1491_termStructuralFromFin_Equation65_parastrophic :
    Law1491.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op y (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law1491.models_iff]
    exact fun x y ↦ @aux65_1491 G _ M h x y
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), funext fun z ↦ (@inv65_73f9f1faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3862 `x ◇ x = (x ◇ (x ◇ x)) ◇ x` holds of the term `x □ y := x ◇ ((y ◇ (x ◇ y)) ◇ y)`
over any finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_3862 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x ◇ ((x ◇ (x ◇ x)) ◇ x) = (x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ ((x ◇ ((x ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      x)) ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ◇ ((x ◇ (x ◇ x)) ◇ x) ≠ (x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ ((x ◇ ((x ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      x)) ◇ x) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose ef6 ef6
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef12 :
      x ◇ ((x ◇ (x ◇ x)) ◇ x) ≠ (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      ((x ◇ ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ x)) ◇ x) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef14 :
      x ◇ ((x ◇ (x ◇ x)) ◇ x) ≠ x ◇
      ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ x) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef15 : x ◇ ((x ◇ (x ◇ x)) ◇ x) ≠ x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x) := by
    first | exact superpose ef6 ef14 | exact superpose ef14 ef6
  have ef16 : x ◇ (x ◇ x) ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef11 ef15 | exact superpose ef15 ef11
  subsumption ef16 ef10

theorem Equation3862_termStructuralFromFin_Equation65_parastrophic :
    Law3862.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op y (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law3862.models_iff]
    exact fun x ↦ @aux65_3862 G _ M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), funext fun z ↦ (@inv65_73f9f1faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 4065 `x ◇ x = ((x ◇ x) ◇ x) ◇ x` holds of the term `x □ y := x ◇ ((y ◇ (x ◇ y)) ◇ y)`
over any finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_4065 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x ◇ ((x ◇ (x ◇ x)) ◇ x) =
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇
      ((x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ◇ ((x ◇ (x ◇ x)) ◇ x) ≠ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇
      ((x ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇
      x) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose ef6 ef6
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef13 :
      x ◇ (x ◇ x) ≠ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇
      ((x ◇ (((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x)) ◇ x) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef17 : x ◇ (x ◇ x) ≠ x ◇ (((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ x) := by
    first | exact superpose ef9 ef13 | exact superpose ef13 ef9
  have ef18 : x ◇ (x ◇ x) ≠ x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x) := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  have ef19 : x ◇ (x ◇ x) ≠ x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef9 ef18 | exact superpose ef18 ef9
  subsumption ef19 ef9

theorem Equation4065_termStructuralFromFin_Equation65_parastrophic :
    Law4065.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op y (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law4065.models_iff]
    exact fun x ↦ @aux65_4065 G _ M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), funext fun z ↦ (@inv65_73f9f1faf G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := x ◇ ((y ◇ (x ◇ x)) ◇ (x ◇ x))` of equation 66
`x = y ◇ (x ◇ (y ◇ y))` can be undone: the operation is recovered as
`x ◇ y = ((x ◇ (y ◇ x)) ◇ y) ◇ x` read in `□`. -/
private theorem inv66_1c4da5b9 [Magma G] (h : Equation66 G) (x y : G) :
    ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((y ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((x ◇ (((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((y ◇ ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((y ◇ ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))))) ◇
      (((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((y ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((y ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))))) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((y ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((x ◇ (((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((y ◇ ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((y ◇ ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))))) ◇
      (((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((y ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((y ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))))) ≠ x ◇ y := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef11 :
      x ◇ (((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((y ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((y ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ ((x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (x ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))))) ≠ x ◇ y := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef12 :
      x ◇ y ≠ x ◇ ((y ◇ ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇ (y ◇
      ((x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (x ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)))))) := by
    first | exact superpose ef5 ef11 | exact superpose ef11 ef5
  have ef16 :
      x ◇ y ≠ x ◇ ((y ◇ (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)))) ◇ (y ◇
      (((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x))))) := by
    first | exact superpose ef5 ef12 | exact superpose ef12 ef5
  have ef20 :
      x ◇ y ≠ x ◇ ((y ◇ (((x ◇ (y ◇ y)) ◇ (x ◇ x)) ◇ ((x ◇ (y ◇ y)) ◇ (x ◇ x)))) ◇
      (y ◇ (((x ◇ (y ◇ y)) ◇ (x ◇ x)) ◇ ((x ◇ (y ◇ y)) ◇ (x ◇ x))))) := by
    first | exact superpose ef5 ef16 | exact superpose ef16 ef5
  have ef24 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef28 (X0 X1 : G) : X1 ◇ X1 = ((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0 := superpose ef24 ef24
  have ef34 (X0 X1 : G) :
      X1 ◇ X1 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose ef28 ef28
  have ef36 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ X0) = (X1 ◇ X1) ◇ (X0 ◇ X0) := by
    first | exact superpose ef28 ef24 | exact superpose ef24 ef28
  have ef37 (X0 X1 : G) : X1 ◇ X1 = X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef34 | exact superpose ef34 ef7
  have ef43 (X0 X1 : G) : (X0 ◇ X1) ◇ (X0 ◇ X0) = X1 := by
    first | exact superpose ef37 ef5 | exact superpose ef5 ef37
  have ef64 :
      x ◇ y ≠ x ◇ ((y ◇ y) ◇ ((((x ◇ (y ◇ y)) ◇ (x ◇ x)) ◇ ((x ◇ (y ◇ y)) ◇ (x ◇ x))) ◇
      (((x ◇ (y ◇ y)) ◇ (x ◇ x)) ◇ ((x ◇ (y ◇ y)) ◇ (x ◇ x))))) := by
    first | exact superpose ef36 ef20 | exact superpose ef20 ef36
  have ef87 : x ◇ y ≠ x ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ (x ◇ x))) := by
    first | exact superpose ef7 ef64 | exact superpose ef64 ef7
  have ef97 : x ◇ y ≠ x ◇ ((y ◇ y) ◇ (y ◇ y)) := by
    first | exact superpose ef43 ef87 | exact superpose ef87 ef43
  have ef103 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef7 ef97 | exact superpose ef97 ef7
  exact absurd rfl ef103

/-- Equation 53 `x = x ◇ (y ◇ (x ◇ y))` holds of the term `x □ y := x ◇ ((y ◇ (x ◇ x)) ◇ (x ◇ x))`
over any magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_53 [Magma G] (h : Equation66 G) (x y : G) :
    x = x ◇ (((y ◇ (((x ◇ ((y ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇ (x ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ x ◇ (((y ◇ (((x ◇ ((y ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      (x ◇ x)) := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef10 : x ≠ x ◇ ((((x ◇ ((y ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)) ◇ (x ◇ x)) ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef11 : x ≠ ((x ◇ ((y ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ y)) ◇ (x ◇ x) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef14 : x ≠ ((y ◇ (x ◇ x)) ◇ (y ◇ y)) ◇ (x ◇ x) := by
    first | exact superpose ef5 ef11 | exact superpose ef11 ef5
  have ef17 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef21 (X0 X1 : G) : X1 ◇ X1 = ((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0 := superpose ef17 ef17
  have ef27 (X0 X1 : G) :
      X1 ◇ X1 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose ef21 ef21
  have ef30 (X0 X1 : G) : X1 ◇ X1 = X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef27 | exact superpose ef27 ef7
  have ef36 (X0 X1 : G) : (X0 ◇ X1) ◇ (X0 ◇ X0) = X1 := by
    first | exact superpose ef30 ef5 | exact superpose ef5 ef30
  have ef96 : x ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef36 ef14 | exact superpose ef14 ef36
  subsumption ef96 ef7

theorem Equation53_termStructuralFrom_Equation66_parastrophic :
    Law53.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op y (M.op x x)) (M.op x x)))⟩, ?_, ?_, ?_⟩
  · rw [@Law53.models_iff]
    exact fun x y ↦ @aux66_53 G M h x y
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 0) (Term.var 0)))), rfl⟩
  · exact ⟨(tm (tm (tm (Term.var 0) (tm (Term.var 1) (Term.var 0))) (Term.var 1)) (Term.var 0)), funext fun z ↦ (@inv66_1c4da5b9 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (y ◇ y) ◇ x` of equation 66 `x = y ◇ (x ◇ (y ◇ y))` can be undone:
the operation is recovered as `x ◇ y = y ◇ ((x ◇ x) ◇ x)` read in `□`. -/
private theorem inv66_dfe2c1ca [Magma G] (h : Equation66 G) (x y : G) :
    (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ y = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ y ≠ x ◇ y := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef13 : x ◇ y ≠ ((x ◇ x) ◇ (x ◇ x)) ◇ y := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef15 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef7 ef13 | exact superpose ef13 ef7
  exact absurd rfl ef15

/-- Equation 2494 `x = (y ◇ ((x ◇ x) ◇ x)) ◇ y` holds of the term `x □ y := (y ◇ y) ◇ x` over any
magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_2494 [Magma G] (h : Equation66 G) (x y : G) :
    x = (y ◇ y) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ y) := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef14 : x ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef16 : x ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef8 ef14 | exact superpose ef14 ef8
  subsumption ef16 ef7

theorem Equation2494_termStructuralFrom_Equation66_parastrophic :
    Law2494.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law2494.models_iff]
    exact fun x y ↦ @aux66_2494 G M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv66_dfe2c1ca G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := y ◇ (x ◇ (x ◇ y))` of equation 476 `x = y ◇ (x ◇ (y ◇ (y ◇ x)))` can
be undone: the operation is recovered as `x ◇ y = (x ◇ y) ◇ (x ◇ (x ◇ y))` read in `□` over a
finite carrier. -/
private theorem inv476_18005b30f [Finite G] [Magma G] (h : Equation476 G) (x y : G) :
    ((y ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ (y ◇ (x ◇ (x ◇ y)))))) ◇ ((y ◇ (x ◇ (x ◇ y))) ◇
      ((y ◇ (x ◇ (x ◇ y))) ◇ ((y ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ (y ◇ (x ◇ (x ◇ y)))))))) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ z)))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ◇ y ≠ ((y ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ (y ◇ (x ◇ (x ◇ y)))))) ◇ ((y ◇ (x ◇ (x ◇ y))) ◇
      ((y ◇ (x ◇ (x ◇ y))) ◇
      ((y ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ (y ◇ (x ◇ (x ◇ y)))))))) := mod_symm nh
  have ef11 :
      x ◇ y ≠ ((y ◇ (x ◇ (x ◇ y))) ◇ (x ◇ y)) ◇
      ((y ◇ (x ◇ (x ◇ y))) ◇ ((y ◇ (x ◇ (x ◇ y))) ◇ ((y ◇ (x ◇ (x ◇ y))) ◇ (x ◇ y)))) := by
    first | exact superpose ef6 ef8 | exact superpose ef8 ef6
  subsumption ef11 ef7

/-- Equation 503 `x = y ◇ (y ◇ (x ◇ (y ◇ x)))` holds of the term `x □ y := y ◇ (x ◇ (x ◇ y))` over
any finite magma satisfying equation 476 `x = y ◇ (x ◇ (y ◇ (y ◇ x)))`. -/
private theorem aux476_503 [Finite G] [Magma G] (h : Equation476 G) (x y : G) :
    x = (((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x)))))) ◇ (y ◇ (y ◇
      ((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x))))))))) ◇ (y ◇ (y ◇
      (((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x)))))) ◇
      (y ◇ (y ◇ ((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x))))))))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ z)))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ (((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x)))))) ◇ (y ◇ (y ◇
      ((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x))))))))) ◇ (y ◇ (y ◇
      (((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x)))))) ◇
      (y ◇ (y ◇ ((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x))))))))))) := mod_symm nh
  have ef11 :
      x ≠ (((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x)))))) ◇
      (y ◇ (y ◇ ((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x))))))))) ◇ (y ◇
      ((x ◇ (y ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ x))))))) := by
    first | exact superpose ef6 ef8 | exact superpose ef8 ef6
  have ef12 : x ≠ ((y ◇ (y ◇ x)) ◇ (y ◇ (y ◇ (y ◇ (y ◇ x))))) ◇ (y ◇ (y ◇ (y ◇ x))) := by
    first | exact superpose ef7 ef11 | exact superpose ef11 ef7
  have ef13 : x ≠ (y ◇ x) ◇ (y ◇ (y ◇ (y ◇ x))) := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  subsumption ef13 ef7

theorem Equation503_termStructuralFromFin_Equation476_parastrophic :
    Law503.TermStructuralFromFin Law476 := by
  intro G _ M hGL
  have h : Equation476 G := Law476.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op x (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law503.models_iff]
    exact fun x y ↦ @aux476_503 G _ M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv476_18005b30f G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (x ◇ y) ◇ (x ◇ (x ◇ y))` of equation 503
`x = y ◇ (y ◇ (x ◇ (y ◇ x)))` can be undone: the operation is recovered as
`x ◇ y = y ◇ (x ◇ (x ◇ y))` read in `□` over a finite carrier. -/
private theorem inv503_52c8d385f [Finite G] [Magma G] (h : Equation503 G) (x y : G) :
    (y ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y))))))) ◇
      (y ◇ (y ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))))))) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ (b ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ (b ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ (b ◇ z))) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ◇ y ≠ (y ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y))))))) ◇ (y ◇
      (y ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))))))) := mod_symm nh
  have ef12 :
      x ◇ y ≠ (y ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ y))) ◇
      (y ◇ (y ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ y)))) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef13 : x ◇ y ≠ (y ◇ (y ◇ (x ◇ y))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ y)))) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  subsumption ef13 ef8

/-- Equation 476 `x = y ◇ (x ◇ (y ◇ (y ◇ x)))` holds of the term `x □ y := (x ◇ y) ◇ (x ◇ (x ◇ y))`
over any finite magma satisfying equation 503 `x = y ◇ (y ◇ (x ◇ (y ◇ x)))`. -/
private theorem aux503_476 [Finite G] [Magma G] (h : Equation503 G) (x y : G) :
    x = (y ◇ ((x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x))))))) ◇ (x ◇
      (x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))))))))) ◇ (y ◇ (y ◇
      ((x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x))))))) ◇
      (x ◇ (x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x))))))))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ (b ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ (b ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ (b ◇ z))) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (y ◇ ((x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x))))))) ◇
      (x ◇ (x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))))))))) ◇ (y ◇
      (y ◇ ((x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x))))))) ◇ (x ◇
      (x ◇
      ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x))))))))))) := mod_symm nh
  have ef12 :
      x ≠ (y ◇ ((x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ x))) ◇ (x ◇
      (x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ x)))))) ◇ (y ◇ (y ◇
      ((x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ x))) ◇
      (x ◇ (x ◇ ((y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ x)))) ◇ (y ◇ x))))))) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef13 :
      x ≠ (y ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ x)))))) ◇
      (y ◇ (y ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (y ◇ x))))))) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef14 : x ≠ (y ◇ (y ◇ x)) ◇ (y ◇ (y ◇ (y ◇ x))) := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef14 ef8

theorem Equation476_termStructuralFromFin_Equation503_parastrophic :
    Law476.TermStructuralFromFin Law503 := by
  intro G _ M hGL
  have h : Equation503 G := Law503.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) (M.op x (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law476.models_iff]
    exact fun x y ↦ @aux503_476 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv503_52c8d385f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3862 `x ◇ x = (x ◇ (x ◇ x)) ◇ x` holds of the term `x □ y := (x ◇ y) ◇ (x ◇ (x ◇ y))`
over any finite magma satisfying equation 503 `x = y ◇ (y ◇ (x ◇ (y ◇ x)))`. -/
private theorem aux503_3862 [Finite G] [Magma G] (h : Equation503 G) (x : G) :
    (x ◇ x) ◇ (x ◇ (x ◇ x)) =
      (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ◇ x) ◇
      (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ◇
      (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ◇ x)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ (b ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ (b ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ (b ◇ z))) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (x ◇ x) ◇ (x ◇ (x ◇ x)) ≠ (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇
      (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ◇ x) ◇ (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇
      (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ◇
      (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))) ◇
      x)) := mod_symm nh
  have ef12 :
      (x ◇ x) ◇ (x ◇ (x ◇ x)) ≠ (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇ x) ◇
      (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef13 :
      (x ◇ x) ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef14 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) := superpose ef9 ef9
  have ef21 (X0 X1 : G) :
      X1 ◇ (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef40 : (x ◇ x) ◇ (x ◇ (x ◇ x)) ≠ (x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef48 : (x ◇ x) ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef21 ef40 | exact superpose ef40 ef21
  subsumption ef48 ef14

theorem Equation3862_termStructuralFromFin_Equation503_parastrophic :
    Law3862.TermStructuralFromFin Law503 := by
  intro G _ M hGL
  have h : Equation503 G := Law503.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) (M.op x (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law3862.models_iff]
    exact fun x ↦ @aux503_3862 G _ M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv503_52c8d385f G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := x ◇ ((x ◇ y) ◇ (x ◇ y))` of equation 510
`x = y ◇ (y ◇ (y ◇ (x ◇ x)))` can be undone: the operation is recovered as
`x ◇ y = x ◇ ((x ◇ y) ◇ (x ◇ y))` read in `□`. -/
private theorem inv510_23d3c07e [Magma G] (h : Equation510 G) (x y : G) :
    x ◇ ((x ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇
      (((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y))))))) ◇ (x ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇
      (((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y)))))))) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ y ≠ x ◇ ((x ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇
      (((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y))))))) ◇ (x ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇
      (((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y)))))))) := mod_symm nh
  have ef7 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := superpose ef5 ef5
  have ef8 (X0 : G) :
      ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef10 (X0 : G) : X0 ◇ X0 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef12 (X0 : G) :
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef10 ef5 | exact superpose ef5 ef10
  have ef13 (X0 : G) :
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef16 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 ◇ (X0 ◇ X0) := by
    first | exact superpose ef13 ef8 | exact superpose ef8 ef13
  have ef21 (X0 X1 : G) :
      ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef13 ef5 | exact superpose ef5 ef13
  have ef31 :
      x ◇ y ≠ x ◇ ((x ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y))))))) ◇ (x ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇
      ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ ((x ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y)))))))) := by
    first | exact superpose ef16 ef6 | exact superpose ef6 ef16
  have ef153 (X0 X1 X2 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = X2 ◇ (X2 ◇ (X2 ◇ X1)) := superpose ef21 ef21
  have ef165 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    first | exact superpose ef21 ef13 | exact superpose ef13 ef21
  have ef624 (X0 : G) :
      x ◇ y ≠ x ◇ ((x ◇ (X0 ◇ (X0 ◇ (X0 ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y))))))) ◇
      (x ◇ (X0 ◇ (X0 ◇ (X0 ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y)))))))) := by
    first | exact superpose ef153 ef31 | exact superpose ef31 ef153
  have ef867 : x ◇ y ≠ x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ (x ◇ y)))) := by
    first | exact superpose ef5 ef624 | exact superpose ef624 ef5
  have ef882 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef165 ef867 | exact superpose ef867 ef165
  exact absurd rfl ef882

/-- Equation 439 `x = x ◇ (y ◇ (y ◇ (y ◇ x)))` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ (x ◇ y))`
over any magma satisfying equation 510 `x = y ◇ (y ◇ (y ◇ (x ◇ x)))`. -/
private theorem aux510_439 [Magma G] (h : Equation510 G) (x y : G) :
    x = x ◇ ((x ◇ (y ◇
      ((y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x))))))) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))))))))) ◇ (x ◇ (y ◇
      ((y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x))))))) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x))))))))))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ x ◇ ((x ◇ (y ◇ ((y ◇
      (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x))))))) ◇ (y ◇
      (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))))))))) ◇ (x ◇ (y ◇
      ((y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x))))))) ◇ (y ◇
      (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ x))))))))))) := mod_symm nh
  have ef7 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := superpose ef5 ef5
  have ef8 (X0 : G) :
      ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef10 (X0 : G) : X0 ◇ X0 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef12 (X0 : G) :
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef10 ef5 | exact superpose ef5 ef10
  have ef13 (X0 : G) :
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef15 (X0 : G) :
      ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef13 ef10 | exact superpose ef10 ef13
  have ef16 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 ◇ (X0 ◇ X0) := by
    first | exact superpose ef13 ef8 | exact superpose ef8 ef13
  have ef20 (X0 : G) : X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef13 ef7 | exact superpose ef7 ef13
  have ef21 (X0 X1 : G) :
      ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef13 ef5 | exact superpose ef5 ef13
  have ef24 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef33 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef16 ef8 | exact superpose ef8 ef16
  have ef40 (X0 : G) :
      X0 ◇ X0 = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇
      (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef16 ef8 | exact superpose ef8 ef16
  have ef43 (X0 : G) :
      X0 ◇ X0 = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇
      ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef16 ef40 | exact superpose ef40 ef16
  have ef48 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    first | exact superpose ef24 ef33 | exact superpose ef33 ef24
  have ef52 (X0 : G) :
      X0 ◇ X0 = (X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef24 ef43 | exact superpose ef43 ef24
  have ef56 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0 := by
    first | exact superpose ef48 ef52 | exact superpose ef52 ef48
  have ef166 (X0 X1 X2 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = X2 ◇ (X2 ◇ (X2 ◇ X1)) := superpose ef21 ef21
  have ef177 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    first | exact superpose ef21 ef20 | exact superpose ef20 ef21
  have ef179 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    first | exact superpose ef21 ef8 | exact superpose ef8 ef21
  have ef185 (X0 X1 : G) :
      X1 ◇ X1 = (X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    first | exact superpose ef21 ef8 | exact superpose ef8 ef21
  have ef215 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    first | exact superpose ef16 ef179 | exact superpose ef179 ef16
  have ef265 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef177 | exact superpose ef177 ef5
  have ef632 (X0 X1 : G) : X1 ◇ X1 = (X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1 := by
    first | exact superpose ef166 ef56 | exact superpose ef56 ef166
  have ef715 (X0 X1 : G) :
      (X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ X0)) ◇
      (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    first | exact superpose ef5 ef632 | exact superpose ef632 ef5
  have ef739 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef5 ef632 | exact superpose ef632 ef5
  have ef861 (X0 X1 : G) :
      X1 ◇ (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef215 | exact superpose ef215 ef5
  have ef920 (X0 X1 : G) :
      X1 ◇ (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ X0) := by
    first | exact superpose ef739 ef861 | exact superpose ef861 ef739
  have ef1274 (X0 X1 : G) :
      (X0 ◇ X1) ◇ (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇
      (X0 ◇ X1) := by
    first | exact superpose ef265 ef632 | exact superpose ef632 ef265
  have ef1275 (X0 X1 : G) :
      (X0 ◇ X1) ◇ (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef739 ef1274 | exact superpose ef1274 ef739
  have ef1322 (X0 X1 : G) : X0 ◇ (X1 ◇ X1) = (X0 ◇ X1) ◇ (X0 ◇ X1) := by
    first | exact superpose ef920 ef1275 | exact superpose ef1275 ef920
  have ef1398 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef5 ef1322 | exact superpose ef1322 ef5
  have ef1443 :
      x ≠ x ◇ ((x ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x)))))))))) ◇ (x ◇ (y ◇
      ((y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))))))) := by
    first | exact superpose ef1322 ef6 | exact superpose ef6 ef1322
  have ef1493 :
      x ≠ x ◇ (x ◇ ((y ◇ ((y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))))) ◇ (y ◇
      ((y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))))))) := by
    first | exact superpose ef1322 ef1443 | exact superpose ef1443 ef1322
  have ef1521 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef715 ef1398 | exact superpose ef1398 ef715
  have ef1529 :
      x ≠ x ◇ (x ◇ ((y ◇ (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x)))))))) ◇ (y ◇
      ((y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))))))) := by
    first | exact superpose ef739 ef1493 | exact superpose ef1493 ef739
  have ef1546 :
      x ≠ x ◇ (x ◇ ((y ◇ (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x)))))))) ◇ (y ◇
      ((y ◇ (y ◇ (y ◇ (y ◇ (y ◇ (x ◇ x)))))) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))))))) := by
    first | exact superpose ef715 ef1529 | exact superpose ef1529 ef715
  have ef1555 :
      x ≠ x ◇ (x ◇ ((y ◇ (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x)))))))) ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))) := by
    first | exact superpose ef1521 ef1546 | exact superpose ef1546 ef1521
  have ef1560 :
      x ≠ x ◇ (x ◇ (((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))) ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))) := by
    first | exact superpose ef632 ef1555 | exact superpose ef1555 ef632
  have ef1564 :
      x ≠ x ◇ (x ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ x)))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ x))))))) := by
    first | exact superpose ef16 ef1560 | exact superpose ef1560 ef16
  have ef1568 : x ≠ x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))) := by
    first | exact superpose ef185 ef1564 | exact superpose ef1564 ef185
  have ef1572 : x ≠ x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef16 ef1568 | exact superpose ef1568 ef16
  subsumption ef1572 ef5

theorem Equation439_termStructuralFrom_Equation510_parastrophic :
    Law439.TermStructuralFrom Law510 := by
  intro G M hGL
  have h : Equation510 G := Law510.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law439.models_iff]
    exact fun x y ↦ @aux510_439 G M h x y
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv510_23d3c07e G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := x ◇ (x ◇ (x ◇ y))` of equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))` can
be undone: the operation is recovered as `x ◇ y = x ◇ ((x ◇ y) ◇ x)` read in `□`. -/
private theorem inv546_6e2757bf [Magma G] (h : Equation546 G) (x y : G) :
    x ◇ (x ◇ (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ x))))) = x ◇
      y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ y ≠ x ◇ (x ◇ (x ◇
      ((x ◇ (x ◇ (x ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ x))))) := mod_symm nh
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 : x ◇ y ≠ x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef11 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef84 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  exact absurd rfl ef84

/-- Equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))` holds of the term `x □ y := x ◇ (x ◇ (x ◇ y))` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_556 [Magma G] (h : Equation546 G) (x y z : G) :
    x = y ◇ (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ z))))))))))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ y ◇ (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ z))))))))))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef14 (X0 X1 X2 X3 : G) : X3 ◇ (X0 ◇ (X3 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X1) := by
    first | exact superpose ef5 ef8 | exact superpose ef8 ef5
  have ef20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef21 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0 = X3 := superpose ef8 ef8
  have ef23 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef24 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0)))) = X3 := by
    first | exact superpose ef12 ef23 | exact superpose ef23 ef12
  have ef27 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X1 ◇ X0)) = X3 ◇ (X0 ◇ (X3 ◇ X2)) := by
    first | exact superpose ef12 ef14 | exact superpose ef14 ef12
  have ef185 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ X2 = X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1))) := by
    first | exact superpose ef5 ef20 | exact superpose ef20 ef5
  have ef186 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ X2 = X3 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef10 ef20 | exact superpose ef20 ef10
  have ef512 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X0) ◇ X3 = X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X0)) := by
    first | exact superpose ef10 ef21 | exact superpose ef21 ef10
  have ef577 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) ◇ X3 = ((X1 ◇ X3) ◇ X0) ◇ X2 := by
    first | exact superpose ef186 ef512 | exact superpose ef512 ef186
  have ef727 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ (X1 ◇ X3)) = X0 ◇ (X3 ◇ (X1 ◇ X2)) := by
    first | exact superpose ef24 ef8 | exact superpose ef8 ef24
  have ef901 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ ((X2 ◇ (X4 ◇ X1)) ◇ (X3 ◇ X5)) = X4 ◇
      (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose ef27 ef27
  have ef1021 (X0 : G) :
      x ≠ y ◇ (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ (y ◇ (y ◇ (y ◇ (X0 ◇ (z ◇ (X0 ◇ x))))))))))) := by
    first | exact superpose ef27 ef6 | exact superpose ef6 ef27
  have ef1028 (X0 : G) : x ≠ ((z ◇ (z ◇ (y ◇ (y ◇ (y ◇ (X0 ◇ (z ◇ (X0 ◇ x)))))))) ◇ y) ◇ z := by
    first | exact superpose ef185 ef1021 | exact superpose ef1021 ef185
  have ef1098 (X0 X1 X2 X4 X5 : G) :
      X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X4 ◇ X1) ◇ X5) ◇ X2 := by
    first | exact superpose ef186 ef901 | exact superpose ef901 ef186
  have ef1130 (X0 : G) : x ≠ ((z ◇ z) ◇ y) ◇ (z ◇ (y ◇ (y ◇ (y ◇ (X0 ◇ (z ◇ (X0 ◇ x))))))) := by
    first | exact superpose ef577 ef1028 | exact superpose ef1028 ef577
  have ef1190 (X0 : G) : x ≠ ((((z ◇ z) ◇ y) ◇ y) ◇ z) ◇ (X0 ◇ (z ◇ (X0 ◇ x))) := by
    first | exact superpose ef1098 ef1130 | exact superpose ef1130 ef1098
  have ef1226 (X0 : G) : x ≠ ((((z ◇ z) ◇ y) ◇ y) ◇ z) ◇ (X0 ◇ (x ◇ (X0 ◇ z))) := by
    first | exact superpose ef727 ef1190 | exact superpose ef1190 ef727
  have ef1246 (X0 : G) : x ≠ ((z ◇ z) ◇ z) ◇ (X0 ◇ (x ◇ (X0 ◇ z))) := by
    first | exact superpose ef9 ef1226 | exact superpose ef1226 ef9
  have ef1260 (X0 : G) : x ≠ z ◇ (X0 ◇ (x ◇ (X0 ◇ z))) := by
    first | exact superpose ef9 ef1246 | exact superpose ef1246 ef9
  subsumption ef1260 ef5

theorem Equation556_termStructuralFrom_Equation546_parastrophic :
    Law556.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op x (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law556.models_iff]
    exact fun x y z ↦ @aux546_556 G M h x y z
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), funext fun z ↦ (@inv546_6e2757bf G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := x ◇ ((x ◇ y) ◇ x)` of equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))` can
be undone: the operation is recovered as `x ◇ y = x ◇ (x ◇ (x ◇ y))` read in `□`. -/
private theorem inv556_4b460107 [Magma G] (h : Equation556 G) (x y : G) :
    x ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x))) ◇ x) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 : x ◇ y ≠ x ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x))) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef18 : x ◇ y ≠ x ◇ (x ◇ (x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x)))) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef21 : x ◇ y ≠ (x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x := by
    first | exact superpose ef10 ef18 | exact superpose ef18 ef10
  have ef27 : x ◇ y ≠ x ◇ (x ◇ (x ◇ ((x ◇ y) ◇ x))) := by
    first | exact superpose ef9 ef21 | exact superpose ef21 ef9
  subsumption ef27 ef5

/-- Equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_546 [Magma G] (h : Equation556 G) (x y z : G) :
    x = y ◇ ((y ◇ (z ◇ ((z ◇ (x ◇ ((x ◇ (z ◇ ((z ◇ y) ◇ z))) ◇ x))) ◇ z))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ y ◇ ((y ◇ (z ◇ ((z ◇ (x ◇ ((x ◇ (z ◇ ((z ◇ y) ◇ z))) ◇ x))) ◇ z))) ◇ y) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef22 : x ≠ y ◇ (y ◇ (y ◇ (z ◇ ((z ◇ (x ◇ ((x ◇ (z ◇ ((z ◇ y) ◇ z))) ◇ x))) ◇ z)))) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef23 : x ≠ y ◇ (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ (x ◇ ((x ◇ (z ◇ ((z ◇ y) ◇ z))) ◇ x))))))) := by
    first | exact superpose ef9 ef22 | exact superpose ef22 ef9
  have ef31 : x ≠ y ◇ (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ (x ◇ (x ◇ (x ◇ (z ◇ ((z ◇ y) ◇ z)))))))))) := by
    first | exact superpose ef9 ef23 | exact superpose ef23 ef9
  have ef39 : x ≠ y ◇ (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ (x ◇ (x ◇ (x ◇ (z ◇ (z ◇ (z ◇ y))))))))))) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef47 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef51 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef72 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ (X1 ◇ (X4 ◇ X0))) ◇ X2))) ◇ X0) = X3 := by
    first | exact superpose ef10 ef7 | exact superpose ef7 ef10
  have ef88 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ (X1 ◇ (X4 ◇ X0))) ◇ X2)))) = X3 := by
    first | exact superpose ef51 ef72 | exact superpose ef72 ef51
  have ef367 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef47 ef10 | exact superpose ef10 ef47
  have ef372 (X0 : G) :
      x ≠ y ◇ (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ (X0 ◇ (x ◇ ((z ◇ (z ◇ (z ◇ y))) ◇ X0)))))))) := by
    first | exact superpose ef47 ef39 | exact superpose ef39 ef47
  have ef417 (X0 X1 : G) :
      x ≠ y ◇ (y ◇ (y ◇ (X0 ◇ (z ◇ ((X1 ◇ (x ◇ ((z ◇ (z ◇ (z ◇ y))) ◇ X1))) ◇ X0))))) := by
    first | exact superpose ef47 ef372 | exact superpose ef372 ef47
  have ef420 (X1 : G) : x ≠ z ◇ (y ◇ (X1 ◇ (x ◇ ((z ◇ (z ◇ (z ◇ y))) ◇ X1)))) := by
    first | exact superpose ef367 ef417 | exact superpose ef417 ef367
  subsumption ef420 ef88

theorem Equation546_termStructuralFrom_Equation556_parastrophic :
    Law546.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law546.models_iff]
    exact fun x y z ↦ @aux556_546 G M h x y z
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_4b460107 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := y ◇ (y ◇ (x ◇ y))` of equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))` can
be undone: the operation is recovered as `x ◇ y = ((x ◇ y) ◇ y) ◇ y` read in `□`. -/
private theorem inv714_fe56b280 [Magma G] (h : Equation714 G) (x y : G) :
    y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ (y ◇ (x ◇ y))) ◇ y))) ◇ y)) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : x ◇ y ≠ y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ (y ◇ (x ◇ y))) ◇ y))) ◇ y)) := mod_symm nh
  have ef8 : x ◇ y ≠ y ◇ (y ◇ ((y ◇ (x ◇ y)) ◇ y)) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  subsumption ef8 ef5

/-- Equation 8 `x = x ◇ (x ◇ x)` holds of the term `x □ y := y ◇ (y ◇ (x ◇ y))` over any magma
satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_8 [Magma G] (h : Equation714 G) (x : G) :
    x = (x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef11 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef12 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef11 | exact superpose ef11 ef5
  have ef21 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef23 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef26 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef7 ef23 | exact superpose ef23 ef7
  have ef27 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ x := by
    first | exact superpose ef5 ef26 | exact superpose ef26 ef5
  have ef28 : x ≠ x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef12 ef27 | exact superpose ef27 ef12
  have ef29 : x ≠ x ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef7 ef28 | exact superpose ef28 ef7
  subsumption ef29 ef5

theorem Equation8_termStructuralFrom_Equation714_parastrophic :
    Law8.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law8.models_iff]
    exact fun x ↦ @aux714_8 G M h x
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv714_fe56b280 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := x ◇ ((x ◇ y) ◇ x)` of equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))` can
be undone: the operation is recovered as `x ◇ y = y ◇ (y ◇ (y ◇ x))` read in `□`. -/
private theorem inv714_4b460107 [Magma G] (h : Equation714 G) (x y : G) :
    y ◇ ((y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ y))) ◇ y))) ◇ y) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : y ◇ ((y ◇ (y ◇ ((y ◇ (y ◇ ((y ◇ x) ◇ y))) ◇ y))) ◇ y) ≠ x ◇ y := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef8 : x ◇ y ≠ y ◇ ((y ◇ (y ◇ (x ◇ y))) ◇ y) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef18 : x ◇ y ≠ y ◇ (y ◇ ((y ◇ (x ◇ y)) ◇ y)) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  subsumption ef18 ef5

/-- Equation 23 `x = (x ◇ x) ◇ x` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over any magma
satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_23 [Magma G] (h : Equation714 G) (x : G) :
    x = (x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef11 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef13 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef14 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef13 | exact superpose ef13 ef5
  have ef15 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x) := by
    first | exact superpose ef5 ef11 | exact superpose ef11 ef5
  have ef19 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef14 ef15 | exact superpose ef15 ef14
  have ef22 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef14 ef19 | exact superpose ef19 ef14
  have ef25 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef7 ef22 | exact superpose ef22 ef7
  have ef27 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ x := by
    first | exact superpose ef5 ef25 | exact superpose ef25 ef5
  have ef29 : x ≠ x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef14 ef27 | exact superpose ef27 ef14
  have ef31 : x ≠ x ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef7 ef29 | exact superpose ef29 ef7
  subsumption ef31 ef5

theorem Equation23_termStructuralFrom_Equation714_parastrophic :
    Law23.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law23.models_iff]
    exact fun x ↦ @aux714_23 G M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), funext fun z ↦ (@inv714_4b460107 G M h (z 0) (z 1)).symm⟩

/-- Equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_464 [Magma G] (h : Equation714 G) (x y : G) :
    x = y ◇ ((y ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x))) ◇ x))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ y ◇ ((y ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x))) ◇ x))) ◇ y) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef8 : x ≠ y ◇ ((y ◇ (x ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ x))) ◇ y) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef21 : x ≠ y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ x)) ◇ y)) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef24 : x ≠ y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ (y ◇ x)) ◇ x))) ◇ y)) := by
    first | exact superpose ef7 ef21 | exact superpose ef21 ef7
  have ef34 : x ≠ y ◇ (y ◇ ((y ◇ x) ◇ y)) := by
    first | exact superpose ef5 ef24 | exact superpose ef24 ef5
  subsumption ef34 ef5

theorem Equation464_termStructuralFrom_Equation714_parastrophic :
    Law464.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law464.models_iff]
    exact fun x y ↦ @aux714_464 G M h x y
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), funext fun z ↦ (@inv714_4b460107 G M h (z 0) (z 1)).symm⟩

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_1629 [Magma G] (h : Equation714 G) (x : G) :
    x = (x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇ (x ◇
      ((x ◇ x) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇ (x ◇
      ((x ◇ x) ◇ x))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef14 :
      x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef17 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef18 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef17 | exact superpose ef17 ef5
  have ef20 : x ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef5 ef14 | exact superpose ef14 ef5
  have ef25 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef18 ef20 | exact superpose ef20 ef18
  have ef29 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ x := by
    first | exact superpose ef5 ef25 | exact superpose ef25 ef5
  have ef33 : x ≠ x ◇ (((x ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef18 ef29 | exact superpose ef29 ef18
  have ef35 : x ≠ x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef18 ef33 | exact superpose ef33 ef18
  have ef37 : x ≠ x ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef7 ef35 | exact superpose ef35 ef7
  subsumption ef37 ef5

theorem Equation1629_termStructuralFrom_Equation714_parastrophic :
    Law1629.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1629.models_iff]
    exact fun x ↦ @aux714_1629 G M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), funext fun z ↦ (@inv714_4b460107 G M h (z 0) (z 1)).symm⟩

/-- Equation 1832 `x = (x ◇ (x ◇ x)) ◇ (x ◇ x)` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_1832 [Magma G] (h : Equation714 G) (x : G) :
    x = (x ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x)) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x)) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef8 : x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef17 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef18 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef17 | exact superpose ef17 ef5
  have ef49 : x ≠ (x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef18 ef8 | exact superpose ef8 ef18
  have ef53 (X0 X1 : G) : (X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := by
    first | exact superpose ef18 ef5 | exact superpose ef5 ef18
  subsumption ef49 ef53

theorem Equation1832_termStructuralFrom_Equation714_parastrophic :
    Law1832.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1832.models_iff]
    exact fun x ↦ @aux714_1832 G M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), funext fun z ↦ (@inv714_4b460107 G M h (z 0) (z 1)).symm⟩

/-- Equation 3103 `x = (((y ◇ x) ◇ x) ◇ x) ◇ y` holds of the term `x □ y := y ◇ (y ◇ (x ◇ y))` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_3103 [Magma G] (h : Equation714 G) (x y : G) :
    x = y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ x))) ◇ x))) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ x))) ◇ x))) ◇ y)) := mod_symm nh
  have ef8 : x ≠ y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ (y ◇ x)) ◇ x))) ◇ y)) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef10 : x ≠ y ◇ (y ◇ ((y ◇ x) ◇ y)) := by
    first | exact superpose ef5 ef8 | exact superpose ef8 ef5
  subsumption ef10 ef5

theorem Equation3103_termStructuralFrom_Equation714_parastrophic :
    Law3103.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law3103.models_iff]
    exact fun x y ↦ @aux714_3103 G M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv714_fe56b280 G M h (z 0) (z 1)).symm⟩

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the term `x □ y := y ◇ (y ◇ (x ◇ y))` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_3253 [Magma G] (h : Equation714 G) (x : G) :
    x ◇ (x ◇ (x ◇ x)) = ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ (((x ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ (x ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef11 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef12 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef11 | exact superpose ef11 ef5
  have ef21 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)))) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef23 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef26 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))))) := by
    first | exact superpose ef7 ef23 | exact superpose ef23 ef7
  have ef27 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x))) := by
    first | exact superpose ef5 ef26 | exact superpose ef26 ef5
  have ef28 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) := by
    first | exact superpose ef7 ef27 | exact superpose ef27 ef7
  have ef29 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef28 | exact superpose ef28 ef5
  have ef30 :
      x ◇ (x ◇ (x ◇ x)) ≠ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef29 | exact superpose ef29 ef12
  have ef31 :
      x ◇ (x ◇ (x ◇ x)) ≠ (x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ x)) := by
    first | exact superpose ef7 ef30 | exact superpose ef30 ef7
  have ef32 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef31 | exact superpose ef31 ef5
  exact absurd rfl ef32

theorem Equation3253_termStructuralFrom_Equation714_parastrophic :
    Law3253.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law3253.models_iff]
    exact fun x ↦ @aux714_3253 G M h x
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv714_fe56b280 G M h (z 0) (z 1)).symm⟩

/-- Equation 3319 `x ◇ y = x ◇ (y ◇ (y ◇ y))` holds of the term `x □ y := y ◇ (y ◇ (x ◇ y))` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_3319 [Magma G] (h : Equation714 G) (x y : G) :
    y ◇ (y ◇ (x ◇ y)) = ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇
      (((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇
      (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      y ◇ (y ◇ (x ◇ y)) ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇
      (y ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇ (((y ◇ (y ◇ (y ◇ y))) ◇
      ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇ (x ◇
      ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef11 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef12 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef11 | exact superpose ef11 ef5
  have ef22 :
      y ◇ (y ◇ (x ◇ y)) ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y)))) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef23 :
      y ◇ (y ◇ (x ◇ y)) ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇
      (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y))))) := by
    first | exact superpose ef12 ef22 | exact superpose ef22 ef12
  have ef26 :
      y ◇ (y ◇ (x ◇ y)) ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))))) := by
    first | exact superpose ef7 ef23 | exact superpose ef23 ef7
  have ef27 :
      y ◇ (y ◇ (x ◇ y)) ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ y) ◇
      (((y ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y))) := by
    first | exact superpose ef5 ef26 | exact superpose ef26 ef5
  have ef28 :
      y ◇ (y ◇ (x ◇ y)) ≠ (y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇
      ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (x ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y)))) := by
    first | exact superpose ef12 ef27 | exact superpose ef27 ef12
  have ef29 :
      y ◇ (y ◇ (x ◇ y)) ≠ (y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇
      ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (x ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y))))) := by
    first | exact superpose ef7 ef28 | exact superpose ef28 ef7
  have ef30 : y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇ (x ◇ y)) := by
    first | exact superpose ef5 ef29 | exact superpose ef29 ef5
  exact absurd rfl ef30

theorem Equation3319_termStructuralFrom_Equation714_parastrophic :
    Law3319.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law3319.models_iff]
    exact fun x y ↦ @aux714_3319 G M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv714_fe56b280 G M h (z 0) (z 1)).symm⟩

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_3456 [Magma G] (h : Equation714 G) (x : G) :
    x ◇ ((x ◇ x) ◇ x) = x ◇
      ((x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ ((x ◇ x) ◇ x) ≠ x ◇
      ((x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef12 :
      x ◇ ((x ◇ x) ◇ x) ≠ x ◇
      ((x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))))) ◇ x) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef14 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef15 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef14 | exact superpose ef14 ef5
  have ef16 :
      x ◇ ((x ◇ x) ◇ x) ≠ x ◇
      (x ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇ x)) := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef21 :
      x ◇ ((x ◇ x) ◇ x) ≠ x ◇ (x ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ x)) := by
    first | exact superpose ef5 ef16 | exact superpose ef16 ef5
  have ef25 :
      x ◇ ((x ◇ x) ◇ x) ≠ x ◇ (x ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ x)) := by
    first | exact superpose ef15 ef21 | exact superpose ef21 ef15
  have ef29 :
      x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ x)) := by
    first | exact superpose ef15 ef25 | exact superpose ef25 ef15
  have ef32 :
      x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ x)) := by
    first | exact superpose ef7 ef29 | exact superpose ef29 ef7
  have ef35 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ x)) := by
    first | exact superpose ef5 ef32 | exact superpose ef32 ef5
  have ef38 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) := by
    first | exact superpose ef15 ef35 | exact superpose ef35 ef15
  have ef41 : x ◇ (x ◇ (x ◇ x)) ≠ (x ◇ (x ◇ x)) ◇ x := by
    first | exact superpose ef5 ef38 | exact superpose ef38 ef5
  have ef44 : x ◇ ((x ◇ x) ◇ x) ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef15 ef41 | exact superpose ef41 ef15
  subsumption ef44 ef7

theorem Equation3456_termStructuralFrom_Equation714_parastrophic :
    Law3456.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law3456.models_iff]
    exact fun x ↦ @aux714_3456 G M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), funext fun z ↦ (@inv714_4b460107 G M h (z 0) (z 1)).symm⟩

/-- Equation 3522 `x ◇ y = x ◇ ((y ◇ y) ◇ y)` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_3522 [Magma G] (h : Equation714 G) (x y : G) :
    x ◇ ((x ◇ y) ◇ x) = x ◇
      ((x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ (y ◇ ((y ◇ y) ◇ y))))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ ((x ◇ y) ◇ x) ≠ x ◇
      ((x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ (y ◇ ((y ◇ y) ◇ y))))) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef13 :
      x ◇ ((x ◇ y) ◇ x) ≠ x ◇
      ((x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇ x) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef14 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef15 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef14 | exact superpose ef14 ef5
  have ef16 :
      x ◇ ((x ◇ y) ◇ x) ≠ x ◇
      (x ◇ (((y ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ (y ◇ (y ◇ y))) ◇ y) ◇ (y ◇ (y ◇ (y ◇ y))))) ◇ x)) := by
    first | exact superpose ef7 ef13 | exact superpose ef13 ef7
  have ef21 :
      x ◇ ((x ◇ y) ◇ x) ≠ x ◇
      (x ◇ (((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇ x)) := by
    first | exact superpose ef7 ef16 | exact superpose ef16 ef7
  have ef25 :
      x ◇ ((x ◇ y) ◇ x) ≠ x ◇ (x ◇ (((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ x)) := by
    first | exact superpose ef10 ef21 | exact superpose ef21 ef10
  have ef29 :
      x ◇ ((x ◇ y) ◇ x) ≠ x ◇ (x ◇ (((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇ x)) := by
    first | exact superpose ef15 ef25 | exact superpose ef25 ef15
  have ef32 :
      x ◇ ((x ◇ y) ◇ x) ≠ x ◇ (x ◇ (((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇ x)) := by
    first | exact superpose ef7 ef29 | exact superpose ef29 ef7
  have ef35 : x ◇ ((x ◇ y) ◇ x) ≠ x ◇ (x ◇ (((y ◇ (y ◇ (y ◇ y))) ◇ y) ◇ x)) := by
    first | exact superpose ef5 ef32 | exact superpose ef32 ef5
  have ef38 : x ◇ ((x ◇ y) ◇ x) ≠ x ◇ (x ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x)) := by
    first | exact superpose ef15 ef35 | exact superpose ef35 ef15
  have ef41 : x ◇ ((x ◇ y) ◇ x) ≠ x ◇ (x ◇ ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x)) := by
    first | exact superpose ef7 ef38 | exact superpose ef38 ef7
  have ef44 : x ◇ ((x ◇ y) ◇ x) ≠ x ◇ (x ◇ (y ◇ x)) := by
    first | exact superpose ef5 ef41 | exact superpose ef41 ef5
  subsumption ef44 ef7

theorem Equation3522_termStructuralFrom_Equation714_parastrophic :
    Law3522.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law3522.models_iff]
    exact fun x y ↦ @aux714_3522 G M h x y
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), funext fun z ↦ (@inv714_4b460107 G M h (z 0) (z 1)).symm⟩

/-- Equation 3862 `x ◇ x = (x ◇ (x ◇ x)) ◇ x` holds of the term `x □ y := y ◇ (y ◇ (x ◇ y))` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_3862 [Magma G] (h : Equation714 G) (x : G) :
    x ◇ (x ◇ (x ◇ x)) = x ◇
      (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      x)) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef11 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef12 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef11 | exact superpose ef11 ef5
  have ef21 :
      x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)) ◇ x)) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef23 :
      x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ x)) := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef26 :
      x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ x)) := by
    first | exact superpose ef7 ef23 | exact superpose ef23 ef7
  have ef27 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ x)) := by
    first | exact superpose ef5 ef26 | exact superpose ef26 ef5
  have ef28 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) := by
    first | exact superpose ef12 ef27 | exact superpose ef27 ef12
  have ef29 : x ◇ (x ◇ (x ◇ x)) ≠ (x ◇ (x ◇ x)) ◇ x := by
    first | exact superpose ef5 ef28 | exact superpose ef28 ef5
  have ef30 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef12 ef29 | exact superpose ef29 ef12
  subsumption ef30 ef7

theorem Equation3862_termStructuralFrom_Equation714_parastrophic :
    Law3862.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law3862.models_iff]
    exact fun x ↦ @aux714_3862 G M h x
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv714_fe56b280 G M h (z 0) (z 1)).symm⟩

/-- Equation 3915 `x ◇ y = (x ◇ (x ◇ x)) ◇ y` holds of the term `x □ y := y ◇ (y ◇ (x ◇ y))` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_3915 [Magma G] (h : Equation714 G) (x y : G) :
    y ◇ (y ◇ (x ◇ y)) = y ◇
      (y ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      y)) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef11 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef12 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef11 | exact superpose ef11 ef5
  have ef22 :
      y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)) ◇ y)) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef23 :
      y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ y)) := by
    first | exact superpose ef12 ef22 | exact superpose ef22 ef12
  have ef26 :
      y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ y)) := by
    first | exact superpose ef7 ef23 | exact superpose ef23 ef7
  have ef27 : y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ y)) := by
    first | exact superpose ef5 ef26 | exact superpose ef26 ef5
  have ef28 : y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ y)) := by
    first | exact superpose ef12 ef27 | exact superpose ef27 ef12
  have ef29 : y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ y)) := by
    first | exact superpose ef7 ef28 | exact superpose ef28 ef7
  have ef30 : y ◇ (y ◇ (x ◇ y)) ≠ y ◇ (y ◇ (x ◇ y)) := by
    first | exact superpose ef5 ef29 | exact superpose ef29 ef5
  exact absurd rfl ef30

theorem Equation3915_termStructuralFrom_Equation714_parastrophic :
    Law3915.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y (M.op x y)))⟩, ?_, ?_, ?_⟩
  · rw [@Law3915.models_iff]
    exact fun x y ↦ @aux714_3915 G M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 0) (Term.var 1)))), rfl⟩
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv714_fe56b280 G M h (z 0) (z 1)).symm⟩

/-- Equation 4065 `x ◇ x = ((x ◇ x) ◇ x) ◇ x` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_4065 [Magma G] (h : Equation714 G) (x : G) :
    x ◇ ((x ◇ x) ◇ x) = ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      ((((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ x) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      ((((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ x) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef12 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))))) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef14 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef15 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef14 | exact superpose ef14 ef5
  have ef16 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))))) := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef21 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)))) := by
    first | exact superpose ef5 ef16 | exact superpose ef16 ef5
  have ef25 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef15 ef21 | exact superpose ef21 ef15
  have ef29 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef15 ef25 | exact superpose ef25 ef15
  have ef32 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))))) := by
    first | exact superpose ef7 ef29 | exact superpose ef29 ef7
  have ef35 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x))) := by
    first | exact superpose ef5 ef32 | exact superpose ef32 ef5
  have ef38 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) := by
    first | exact superpose ef7 ef35 | exact superpose ef35 ef7
  have ef41 :
      x ◇ (x ◇ (x ◇ x)) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef38 | exact superpose ef38 ef5
  have ef44 :
      x ◇ (x ◇ (x ◇ x)) ≠ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ x)) := by
    first | exact superpose ef15 ef41 | exact superpose ef41 ef15
  have ef47 :
      x ◇ (x ◇ (x ◇ x)) ≠ (x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ x)) := by
    first | exact superpose ef7 ef44 | exact superpose ef44 ef7
  have ef50 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef47 | exact superpose ef47 ef5
  exact absurd rfl ef50

theorem Equation4065_termStructuralFrom_Equation714_parastrophic :
    Law4065.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4065.models_iff]
    exact fun x ↦ @aux714_4065 G M h x
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), funext fun z ↦ (@inv714_4b460107 G M h (z 0) (z 1)).symm⟩

/-- Equation 4118 `x ◇ y = ((x ◇ x) ◇ x) ◇ y` holds of the term `x □ y := x ◇ ((x ◇ y) ◇ x)` over
any magma satisfying equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. -/
private theorem aux714_4118 [Magma G] (h : Equation714 G) (x y : G) :
    x ◇ ((x ◇ y) ◇ x) = ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      ((((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ y) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ ((x ◇ y) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      ((((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇ y) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X1 ◇ (X1 ◇ (X0 ◇ X1)) := superpose ef5 ef5
  have ef12 :
      x ◇ ((x ◇ y) ◇ x) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ (x ◇ (x ◇ x))))) ◇
      ((((x ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ (x ◇ (x ◇ x))))) ◇ y) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ (x ◇ (x ◇ x)))))) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef13 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef14 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef15 (X0 X1 : G) : (X0 ◇ X1) ◇ X0 = X0 ◇ (X1 ◇ X0) := by
    first | exact superpose ef5 ef14 | exact superpose ef14 ef5
  have ef16 :
      x ◇ ((x ◇ y) ◇ x) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ (x ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ (x ◇ (x ◇ x))))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (x ◇ (x ◇ (x ◇ x))))))) := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef21 :
      x ◇ ((x ◇ y) ◇ x) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef7 ef16 | exact superpose ef16 ef7
  have ef25 :
      x ◇ ((x ◇ y) ◇ x) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)))) := by
    first | exact superpose ef13 ef21 | exact superpose ef21 ef13
  have ef29 :
      x ◇ ((x ◇ y) ◇ x) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef15 ef25 | exact superpose ef25 ef15
  have ef32 :
      x ◇ ((x ◇ y) ◇ x) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))))) := by
    first | exact superpose ef7 ef29 | exact superpose ef29 ef7
  have ef35 :
      x ◇ ((x ◇ y) ◇ x) ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x))) := by
    first | exact superpose ef5 ef32 | exact superpose ef32 ef5
  have ef38 :
      x ◇ ((x ◇ y) ◇ x) ≠ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (y ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) := by
    first | exact superpose ef15 ef35 | exact superpose ef35 ef15
  have ef41 :
      x ◇ ((x ◇ y) ◇ x) ≠ (x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇
      ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))) := by
    first | exact superpose ef7 ef38 | exact superpose ef38 ef7
  have ef44 : x ◇ ((x ◇ y) ◇ x) ≠ x ◇ (x ◇ (y ◇ x)) := by
    first | exact superpose ef5 ef41 | exact superpose ef41 ef5
  subsumption ef44 ef7

theorem Equation4118_termStructuralFrom_Equation714_parastrophic :
    Law4118.TermStructuralFrom Law714 := by
  intro G M hGL
  have h : Equation714 G := Law714.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op (M.op x y) x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4118.models_iff]
    exact fun x y ↦ @aux714_4118 G M h x y
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), funext fun z ↦ (@inv714_4b460107 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (x ◇ x) ◇ (y ◇ y)` of equation 960 `x = y ◇ ((z ◇ y) ◇ (x ◇ x))` can
be undone: the operation is recovered as `x ◇ y = (x ◇ x) ◇ (y ◇ y)` read in `□`. -/
private theorem inv960_dd43a143 [Magma G] (h : Equation960 G) (x y : G) :
    (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) = x ◇
      y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) ≠ x ◇ y := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X1) ◇ (X0 ◇ X1) = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef15 :
      x ◇ y ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef18 : x ◇ y ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y))) := by
    first | exact superpose ef8 ef15 | exact superpose ef15 ef8
  have ef22 : x ◇ y ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y))) := by
    first | exact superpose ef8 ef18 | exact superpose ef18 ef8
  have ef26 : x ◇ y ≠ ((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y))) := by
    first | exact superpose ef8 ef22 | exact superpose ef22 ef8
  have ef46 (X0 X3 : G) : X0 ◇ X0 = (X3 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef70 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef46 ef5 | exact superpose ef5 ef46
  have ef76 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef8 ef70 | exact superpose ef70 ef8
  have ef79 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef8 ef76 | exact superpose ef76 ef8
  have ef108 : x ◇ y ≠ ((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef79 ef26 | exact superpose ef26 ef79
  have ef113 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef79 ef108 | exact superpose ef108 ef79
  exact absurd rfl ef113

/-- Equation 653 `x = x ◇ (y ◇ ((z ◇ y) ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ y)` over
any magma satisfying equation 960 `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`. -/
private theorem aux960_653 [Magma G] (h : Equation960 G) (x y z : G) :
    x = (x ◇ x) ◇ (((y ◇ y) ◇ (((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)))) ◇ ((y ◇ y) ◇
      (((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇ (((y ◇ y) ◇ (((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)))) ◇ ((y ◇ y) ◇
      (((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X1) ◇ (X0 ◇ X1) = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef11 (X0 : G) : X0 ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef14 :
      x ≠ (x ◇ x) ◇ ((((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))) ◇ ((y ◇ y) ◇
      (((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))))) := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef16 (X0 X1 X2 X3 : G) : X1 ◇ X0 = X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef17 :
      x ≠ (x ◇ x) ◇ (((x ◇ x) ◇ ((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))) ◇
      ((y ◇ y) ◇ ((x ◇ x) ◇ ((((z ◇ z) ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))))) := by
    first | exact superpose ef8 ef14 | exact superpose ef14 ef8
  have ef20 :
      x ≠ (x ◇ x) ◇ (((x ◇ x) ◇ (((y ◇ y) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))) ◇
      ((y ◇ y) ◇ ((x ◇ x) ◇ (((y ◇ y) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))))) := by
    first | exact superpose ef8 ef17 | exact superpose ef17 ef8
  have ef26 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X4 ◇ X4)) = X4 := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef27 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X4 ◇ X4)) =
      X4 := superpose ef7 ef7
  have ef31 (X0 X1 X2 X3 X4 : G) : X1 ◇ X0 = ((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef39 (X0 X3 : G) : X0 ◇ X0 = (X3 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef40 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X4 ◇ X4)) = X4 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef41 (X0 X1 X2 X3 : G) :
      (X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef42 (X0 X1 X2 X3 : G) : X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef8 ef41 | exact superpose ef41 ef8
  have ef47 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X4 ◇ X4)) = X4 := by
    first | exact superpose ef8 ef27 | exact superpose ef27 ef8
  have ef56 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0) := by
    first | exact superpose ef8 ef39 | exact superpose ef39 ef8
  have ef133 (X0 X1 X2 : G) : X0 ◇ (X0 ◇ X0) = X1 ◇ ((X2 ◇ X1) ◇ X0) := by
    first | exact superpose ef40 ef5 | exact superpose ef5 ef40
  have ef138 (X0 X1 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef40 ef39 | exact superpose ef39 ef40
  have ef204 (X0 X1 X2 : G) :
      (X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)) = X2 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef16 ef16
  have ef352 (X0 X1 X2 X3 : G) : (X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X2 := by
    first | exact superpose ef133 ef138 | exact superpose ef138 ef133
  have ef354 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X2 := by
    first | exact superpose ef133 ef11 | exact superpose ef11 ef133
  have ef654 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = ((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1) := by
    first | exact superpose ef16 ef31 | exact superpose ef31 ef16
  have ef812 (X0 X1 X2 : G) :
      (X1 ◇ X2) ◇ (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0) := by
    first | exact superpose ef26 ef354 | exact superpose ef354 ef26
  have ef813 (X0 X1 X2 X3 : G) :
      (X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X0) := by
    first | exact superpose ef5 ef354 | exact superpose ef354 ef5
  have ef850 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0) = X0 ◇ (X3 ◇ X0) := by
    first | exact superpose ef654 ef813 | exact superpose ef813 ef654
  have ef851 (X0 X1 X2 : G) : (X1 ◇ X2) ◇ (X0 ◇ X0) = X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0) := by
    first | exact superpose ef654 ef812 | exact superpose ef812 ef654
  have ef874 (X0 X1 X2 X5 X6 : G) :
      (X5 ◇ X6) ◇ (X6 ◇ (X5 ◇ X6)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X5 ◇ X6)) := by
    first | exact superpose ef31 ef42 | exact superpose ef42 ef31
  have ef1046 (X0 X1 X2 X5 X6 : G) :
      (X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X5 ◇ X6)) = X6 ◇ (X6 ◇ (X5 ◇ X6)) := by
    first | exact superpose ef204 ef874 | exact superpose ef874 ef204
  have ef2270 (X0 X1 X2 X3 : G) :
      (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) = X2 ◇
      ((X3 ◇ X2) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    first | exact superpose ef47 ef42 | exact superpose ef42 ef47
  have ef2308 (X0 X1 X2 : G) :
      (X1 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = X2 := by
    first | exact superpose ef47 ef40 | exact superpose ef40 ef47
  have ef2321 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef850 ef2308 | exact superpose ef2308 ef850
  have ef2344 (X0 X1 X2 X3 : G) :
      (X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) = X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    first | exact superpose ef1046 ef2270 | exact superpose ef2270 ef1046
  have ef2444 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    first | exact superpose ef56 ef2344 | exact superpose ef2344 ef56
  have ef2533 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X0) := by
    first | exact superpose ef40 ef2321 | exact superpose ef2321 ef40
  have ef2558 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = (X3 ◇ X2) ◇ X0 := by
    first | exact superpose ef352 ef2321 | exact superpose ef2321 ef352
  have ef2656 (X0 X1 X2 X3 : G) : X3 ◇ (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X0) := by
    first | exact superpose ef39 ef2533 | exact superpose ef2533 ef39
  have ef2681 (X0 X3 : G) : X3 ◇ (X0 ◇ X0) = X0 ◇ ((X3 ◇ X3) ◇ X0) := by
    first | exact superpose ef850 ef2656 | exact superpose ef2656 ef850
  have ef3210 (X0 : G) :
      x ≠ (x ◇ x) ◇ (((x ◇ x) ◇ (((y ◇ y) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))) ◇
      ((X0 ◇ y) ◇ ((x ◇ x) ◇ (((y ◇ y) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))))) := by
    first | exact superpose ef2558 ef20 | exact superpose ef20 ef2558
  have ef3264 (X0 X1 X2 X3 X4 X5 : G) :
      (X4 ◇ X5) ◇ (X5 ◇ (X4 ◇ X5)) = (X0 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5)) := by
    first | exact superpose ef2558 ef42 | exact superpose ef42 ef2558
  have ef3308 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ (X5 ◇ (X4 ◇ X5)) = (X0 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5)) := by
    first | exact superpose ef204 ef3264 | exact superpose ef3264 ef204
  have ef3325 (X0 : G) :
      x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((X0 ◇ y) ◇ ((x ◇ x) ◇ (((y ◇ y) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x))))) := by
    first | exact superpose ef204 ef3210 | exact superpose ef3210 ef204
  have ef3427 (X0 : G) :
      x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((X0 ◇ y) ◇ (((z ◇ z) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef851 ef3325 | exact superpose ef3325 ef851
  have ef3464 :
      x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ ((z ◇ z) ◇ (y ◇ y))) ◇ (x ◇ x)) ◇
      ((x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef3308 ef3427 | exact superpose ef3427 ef3308
  have ef3492 : x ≠ (x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    first | exact superpose ef2444 ef3464 | exact superpose ef3464 ef2444
  have ef3520 : x ≠ x ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    first | exact superpose ef2681 ef3492 | exact superpose ef3492 ef2681
  subsumption ef3520 ef5

theorem Equation653_termStructuralFrom_Equation960_parastrophic :
    Law653.TermStructuralFrom Law960 := by
  intro G M hGL
  have h : Equation960 G := Law960.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y y))⟩, ?_, ?_, ?_⟩
  · rw [@Law653.models_iff]
    exact fun x y z ↦ @aux960_653 G M h x y z
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv960_dd43a143 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := y ◇ (x ◇ y)` of equation 1491 `x = (y ◇ x) ◇ (y ◇ (y ◇ x))` can be
undone: the operation is recovered as `x ◇ y = x ◇ ((y ◇ (x ◇ y)) ◇ y)` read in `□`. -/
private theorem inv1491_f3ffbbdd [Magma G] (h : Equation1491 G) (x y : G) :
    (y ◇ (((y ◇ (x ◇ y)) ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y)) ◇
      (x ◇ (y ◇ (((y ◇ (x ◇ y)) ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y))) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      x ◇ y ≠ (y ◇ (((y ◇ (x ◇ y)) ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y)) ◇
      (x ◇ (y ◇ (((y ◇ (x ◇ y)) ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y))) := mod_symm nh
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef5 ef5
  have ef8 : x ◇ y ≠ (y ◇ ((x ◇ y) ◇ y)) ◇ (x ◇ (y ◇ ((x ◇ y) ◇ y))) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef15 : x ◇ y ≠ (x ◇ (x ◇ y)) ◇ (x ◇ (x ◇ (x ◇ y))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  subsumption ef15 ef5

/-- Equation 65 `x = y ◇ (x ◇ (y ◇ x))` holds of the term `x □ y := y ◇ (x ◇ y)` over any magma
satisfying equation 1491 `x = (y ◇ x) ◇ (y ◇ (y ◇ x))`. -/
private theorem aux1491_65 [Magma G] (h : Equation1491 G) (x y : G) :
    x = ((x ◇ (y ◇ x)) ◇ (x ◇ (x ◇ (y ◇ x)))) ◇ (y ◇ ((x ◇ (y ◇ x)) ◇ (x ◇ (x ◇ (y ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ (y ◇ x)) ◇ (x ◇ (x ◇ (y ◇ x)))) ◇
      (y ◇ ((x ◇ (y ◇ x)) ◇ (x ◇ (x ◇ (y ◇ x))))) := mod_symm nh
  have ef8 : x ≠ (y ◇ x) ◇ (y ◇ (y ◇ x)) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  subsumption ef8 ef5

theorem Equation65_termStructuralFrom_Equation1491_parastrophic :
    Law65.TermStructuralFrom Law1491 := by
  intro G M hGL
  have h : Equation1491 G := Law1491.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op x y))⟩, ?_, ?_, ?_⟩
  · rw [@Law65.models_iff]
    exact fun x y ↦ @aux1491_65 G M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 0) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (tm (Term.var 1) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), funext fun z ↦ (@inv1491_f3ffbbdd G M h (z 0) (z 1)).symm⟩

end Law.MagmaLaw
