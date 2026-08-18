import equational_theories.Definability.FiniteFlavour
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Term-definability facts that hold only over finite magmas

Each source law here has the shape `x = h_k (⋯ (h_1 x) ⋯)`, where every `h_i : G → G` is built
from the magma operation and the law's other variables. The law therefore says that a particular
composite of maps is the identity. On a finite carrier that is much stronger than it looks: the
composite is surjective, so its outermost factor is surjective, so by `Finite.injective_iff_
surjective` that factor is a bijection, and peeling it off shows the cyclic rotation
`h_{k-1} ∘ ⋯ ∘ h_1 ∘ h_k` is the identity too. Iterating, every cyclic rotation of the chain is an
identity of the magma.

Those rotations are genuinely new equations -- they do not follow from the source law over
arbitrary magmas -- and the defining terms below need them. So the facts are stated with
`Law.MagmaLaw.TermDefinableFromFin`, the finite flavour of `TermDefinableFrom`, and not with
`TermDefinableFrom` itself.

Each cell contributes a `private` lemma carrying the equational content `s + rotations ⊢
t[◇ := w]`, replayed from a Vampire refutation in the style of `Generated/VampireProven`, and a
packaging theorem naming the term. The rotations appear as local `have`s, all of them instances of
the single lemma `rot_of_finite`.

The companion file `Definability/PositiveTerms.lean` holds the cells whose defining term needs
only the source law, and which are therefore true over every magma.
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
cyclic rotations. Applied with `f` the outer part of the chain and `g` its first factor, it moves
`g` from the inside of the composite to the outside. -/
private theorem rot_of_finite [Finite G] {f g : G → G} (hfg : ∀ z, f (g z) = z) (x : G) :
    g (f x) = x := by
  have hs : Function.Surjective f := fun z ↦ ⟨g z, hfg z⟩
  exact Finite.injective_iff_surjective.mpr hs (hfg (f x))

/-- Equation 73 `x = y ◇ (y ◇ (x ◇ y))` is term-definable from equation 63 `x = y ◇ (x ◇ (x ◇ y))`
over finite magmas, via the term `x □ y := y ◇ (y ◇ x)`. -/
private theorem aux63_73 [Finite G] [Magma G] (h : Equation63 G) (x y : G) :
    x = ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y)) ◇ (((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y)) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y)) ◇
      (((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y)) ◇ y) := mod_symm nh
  have ef15 : x ≠ (y ◇ x) ◇ ((y ◇ x) ◇ y) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  subsumption ef15 ef7

theorem Equation73_termDefinableFromFin_Equation63 : Law73.TermDefinableFromFin Law63 := by
  intro G _ M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y x))⟩, ?_, ?_⟩
  · rw [@Law73.models_iff]
    exact fun x y ↦ @aux63_73 G _ M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), rfl⟩

/-- Equation 63 `x = y ◇ (x ◇ (x ◇ y))` is term-definable from equation 73 `x = y ◇ (y ◇ (x ◇ y))`
over finite magmas, via the term `x □ y := (x ◇ y) ◇ x`. -/
private theorem aux73_63 [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    x = (y ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ (y ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ y := mod_symm nh
  have ef17 : x ≠ (y ◇ (y ◇ x)) ◇ y := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  subsumption ef17 ef8

theorem Equation63_termDefinableFromFin_Equation73 : Law63.TermDefinableFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_⟩
  · rw [@Law63.models_iff]
    exact fun x y ↦ @aux73_63 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩

/-- Equation 1685 `x = (y ◇ x) ◇ ((x ◇ y) ◇ y)` is term-definable from equation 73
`x = y ◇ (y ◇ (x ◇ y))` over finite magmas, via the term `x □ y := (y ◇ x) ◇ y`. -/
private theorem aux73_1685 [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    x = (((y ◇ ((y ◇ x) ◇ y)) ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (((y ◇ ((y ◇ x) ◇ y)) ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ y) := mod_symm nh
  have ef17 : x ≠ ((x ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ (x ◇ y) := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  subsumption ef17 ef8

theorem Equation1685_termDefinableFromFin_Equation73 : Law1685.TermDefinableFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_⟩
  · rw [@Law1685.models_iff]
    exact fun x y ↦ @aux73_1685 G _ M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩

/-- Equation 3548 `x ◇ y = y ◇ ((x ◇ y) ◇ x)` is term-definable from equation 73
`x = y ◇ (y ◇ (x ◇ y))` over finite magmas, via the term `x □ y := x ◇ (x ◇ y)`. -/
private theorem aux73_3548 [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    x ◇ (x ◇ y) = y ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ x))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ◇ (x ◇ y) ≠ y ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ x))) := mod_symm nh
  have ef14 : x ◇ (x ◇ y) ≠ y ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y)) := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  subsumption ef14 ef7

theorem Equation3548_termDefinableFromFin_Equation73 : Law3548.TermDefinableFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op x y))⟩, ?_, ?_⟩
  · rw [@Law3548.models_iff]
    exact fun x y ↦ @aux73_3548 G _ M h x y
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), rfl⟩

/-- Equation 511 `x = y ◇ (y ◇ (y ◇ (x ◇ y)))` is term-definable from equation 464
`x = y ◇ (x ◇ (x ◇ (x ◇ y)))` over finite magmas, via the term `x □ y := y ◇ (y ◇ (y ◇ x))`. -/
private theorem aux464_511 [Finite G] [Magma G] (h : Equation464 G) (x y : G) :
    x = (((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ (((y ◇
      (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ (((y ◇ (y ◇ (y ◇ x))) ◇
      ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ y))) ◇ ((((y ◇ (y ◇ (y ◇ x))) ◇
      ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ (((y ◇ (y ◇ (y ◇ x))) ◇
      ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ y))) ◇
      ((((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ y))) ◇ y)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ ((b ◇ a) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (z ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ (((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ (((y ◇
      (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ (((y ◇ (y ◇ (y ◇ x))) ◇
      ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ y))) ◇ ((((y ◇ (y ◇ (y ◇ x))) ◇
      ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ (((y ◇ (y ◇ (y ◇ x))) ◇
      ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ y))) ◇
      ((((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ x))) ◇ y))) ◇ y))) ◇
      y)) := mod_symm nh
  have ef20 :
      x ≠ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y))) ◇
      (((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y))) ◇
      (((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y))) ◇ y)) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef21 : x ≠ (y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y)) := by
    first | exact superpose ef7 ef20 | exact superpose ef20 ef7
  subsumption ef21 ef7

theorem Equation511_termDefinableFromFin_Equation464 : Law511.TermDefinableFromFin Law464 := by
  intro G _ M hGL
  have h : Equation464 G := Law464.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y (M.op y x)))⟩, ?_, ?_⟩
  · rw [@Law511.models_iff]
    exact fun x y ↦ @aux464_511 G _ M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), rfl⟩

/-- Equation 3472 `x ◇ x = y ◇ ((x ◇ x) ◇ y)` is term-definable from equation 477
`x = y ◇ (x ◇ (y ◇ (y ◇ y)))` over finite magmas, via the term
`x □ y := ((y ◇ x) ◇ (y ◇ x)) ◇ (y ◇ x)`. -/
private theorem aux477_3472 [Finite G] [Magma G] (h : Equation477 G) (x y : G) :
    ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) =
      (((((y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y)) ◇ ((((y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇
      x) ≠ (((((y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y) ◇
      ((((y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ y)) ◇ ((((y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      y) := mod_symm nh
  have ef9 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X1) = X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose ef7 ef7
  have ef15 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef17 (X0 X1 : G) :
      (X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)) := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef48 (X0 : G) :
      (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇
      ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef15 ef9 | exact superpose ef9 ef15
  have ef50 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef7 ef48 | exact superpose ef48 ef7
  have ef70 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := by
    first | exact superpose ef17 ef6 | exact superpose ef6 ef17
  have ef137 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)) = X1 := by
    first | exact superpose ef50 ef6 | exact superpose ef6 ef50
  have ef138 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0) = X1 := by
    first | exact superpose ef50 ef7 | exact superpose ef7 ef50
  have ef253 :
      x ◇ x ≠ (((((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y)) ◇
      ((((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ (y ◇ (x ◇ x))) ◇ y) := by
    first | exact superpose ef138 ef8 | exact superpose ef8 ef138
  have ef403 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := by
    first | exact superpose ef137 ef70 | exact superpose ef70 ef137
  have ef1153 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef137 ef403 | exact superpose ef403 ef137
  have ef1385 (X0 X1 : G) :
      (X1 ◇ X1) ◇ X1 = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0 := superpose ef1153 ef1153
  have ef5068 :
      x ◇ x ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) := by
    first | exact superpose ef1385 ef253 | exact superpose ef253 ef1385
  have ef5073 (X0 X1 : G) :
      (X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0) := by
    first | exact superpose ef1385 ef137 | exact superpose ef137 ef1385
  have ef5090 (X0 X1 : G) :
      ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0) = ((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef1385 ef1153 | exact superpose ef1153 ef1385
  have ef5102 : x ◇ x ≠ ((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) := by
    first | exact superpose ef5073 ef5068 | exact superpose ef5068 ef5073
  have ef5155 : x ◇ x ≠ ((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef5090 ef5102 | exact superpose ef5102 ef5090
  have ef5194 : x ◇ x ≠ ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) := by
    first | exact superpose ef1153 ef5155 | exact superpose ef5155 ef1153
  subsumption ef5194 ef138

theorem Equation3472_termDefinableFromFin_Equation477 : Law3472.TermDefinableFromFin Law477 := by
  intro G _ M hGL
  have h : Equation477 G := Law477.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y x) (M.op y x)) (M.op y x))⟩, ?_, ?_⟩
  · rw [@Law3472.models_iff]
    exact fun x y ↦ @aux477_3472 G _ M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 0)) (tm (Term.var 1) (Term.var 0))) (tm (Term.var 1) (Term.var 0))), rfl⟩

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` is term-definable from equation 477
`x = y ◇ (x ◇ (y ◇ (y ◇ y)))` over finite magmas, via the term `x □ y := ((x ◇ x) ◇ x) ◇ y`. -/
private theorem aux477_4273 [Finite G] [Magma G] (h : Equation477 G) (x y : G) :
    ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) = ((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) ≠ ((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := mod_symm nh
  have ef9 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X1) = X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose ef7 ef7
  have ef15 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef17 (X0 X1 : G) :
      (X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)) := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef48 (X0 : G) :
      (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇
      ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef15 ef9 | exact superpose ef9 ef15
  have ef50 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef7 ef48 | exact superpose ef48 ef7
  have ef69 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := by
    first | exact superpose ef17 ef6 | exact superpose ef6 ef17
  have ef137 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)) = X1 := by
    first | exact superpose ef50 ef6 | exact superpose ef6 ef50
  have ef306 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := by
    first | exact superpose ef137 ef69 | exact superpose ef69 ef137
  have ef1031 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef137 ef306 | exact superpose ef306 ef137
  have ef1272 : (x ◇ x) ◇ x ≠ ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef1031 ef8 | exact superpose ef8 ef1031
  subsumption ef1272 ef1031

theorem Equation4273_termDefinableFromFin_Equation477 : Law4273.TermDefinableFromFin Law477 := by
  intro G _ M hGL
  have h : Equation477 G := Law477.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_⟩
  · rw [@Law4273.models_iff]
    exact fun x y ↦ @aux477_4273 G _ M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩

/-- Equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` is term-definable from equation 511
`x = y ◇ (y ◇ (y ◇ (x ◇ y)))` over finite magmas, via the term `x □ y := (x ◇ (x ◇ y)) ◇ x`. -/
private theorem aux511_464 [Finite G] [Magma G] (h : Equation511 G) (x y : G) :
    x = (y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇ x))) ◇ x))) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (b ◇ z))) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have hrot2 (a b : G) : b ◇ (b ◇ ((b ◇ a) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((b ◇ z) ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot1 z b) a
  have ef8 (X0 X1 : G) : X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef11 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (hrot2 ..)
  have ef12 :
      x ≠ (y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇ x))) ◇ x))) ◇ y := mod_symm nh
  have ef16 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef24 : x ≠ (y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x))) ◇ y := by
    first | exact superpose ef10 ef12 | exact superpose ef12 ef10
  have ef27 : x ≠ y ◇ ((y ◇ ((x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x)) ◇ y) := by
    first | exact superpose ef16 ef24 | exact superpose ef24 ef16
  have ef31 : x ≠ y ◇ (y ◇ (((x ◇ (x ◇ ((x ◇ y) ◇ x))) ◇ x) ◇ y)) := by
    first | exact superpose ef16 ef27 | exact superpose ef27 ef16
  have ef34 : x ≠ y ◇ (y ◇ ((x ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ y)) := by
    first | exact superpose ef16 ef31 | exact superpose ef31 ef16
  have ef36 : x ≠ y ◇ (y ◇ ((x ◇ (x ◇ (((x ◇ y) ◇ x) ◇ x))) ◇ y)) := by
    first | exact superpose ef16 ef34 | exact superpose ef34 ef16
  have ef38 : x ≠ y ◇ (y ◇ ((x ◇ (x ◇ ((x ◇ (y ◇ x)) ◇ x))) ◇ y)) := by
    first | exact superpose ef16 ef36 | exact superpose ef36 ef16
  have ef40 : x ≠ y ◇ (y ◇ ((y ◇ x) ◇ y)) := by
    first | exact superpose ef11 ef38 | exact superpose ef38 ef11
  subsumption ef40 ef11

theorem Equation464_termDefinableFromFin_Equation511 : Law464.TermDefinableFromFin Law511 := by
  intro G _ M hGL
  have h : Equation511 G := Law511.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x (M.op x y)) x)⟩, ?_, ?_⟩
  · rw [@Law464.models_iff]
    exact fun x y ↦ @aux511_464 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 1))) (Term.var 0)), rfl⟩

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` is term-definable from equation 680
`x = y ◇ (x ◇ ((y ◇ y) ◇ y))` over finite magmas, via the term `x □ y := (x ◇ (x ◇ x)) ◇ y`. -/
private theorem aux680_4273 [Finite G] [Magma G] (h : Equation680 G) (x y : G) :
    (x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x) = (y ◇ (y ◇ y)) ◇ ((x ◇ (x ◇ x)) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ b) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ ((b ◇ b) ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      (x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x) ≠ (y ◇ (y ◇ y)) ◇ ((x ◇ (x ◇ x)) ◇ y) := mod_symm nh
  have ef10 (X0 X1 : G) :
      (X1 ◇ X1) ◇ X1 = X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose ef7 ef7
  have ef18 (X0 X1 : G) :
      ((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1) = ((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) := by
    first | exact superpose ef10 ef7 | exact superpose ef7 ef10
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X2 := by
    first | exact superpose ef18 ef6 | exact superpose ef6 ef18
  have ef135 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef30 | exact superpose ef30 ef7
  have ef188 : x ◇ (x ◇ x) ≠ (x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef135 ef8 | exact superpose ef8 ef135
  subsumption ef188 ef135

theorem Equation4273_termDefinableFromFin_Equation680 : Law4273.TermDefinableFromFin Law680 := by
  intro G _ M hGL
  have h : Equation680 G := Law680.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x (M.op x x)) y)⟩, ?_, ?_⟩
  · rw [@Law4273.models_iff]
    exact fun x y ↦ @aux680_4273 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), rfl⟩

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` is term-definable from equation 873
`x = y ◇ ((x ◇ x) ◇ (y ◇ y))` over finite magmas, via the term `x □ y := ((x ◇ x) ◇ x) ◇ y`. -/
private theorem aux873_4273 [Finite G] [Magma G] (h : Equation873 G) (x y : G) :
    ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) = ((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) :
      (X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (hrot0 ..)
  have ef10 :
      ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) ≠ ((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := mod_symm nh
  have ef14 (X0 : G) : ((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0) = X0 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef24 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0) = X1 := by
    first | exact superpose ef14 ef7 | exact superpose ef7 ef14
  have ef47 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1) := by
    first | exact superpose ef8 ef24 | exact superpose ef24 ef8
  have ef862 (X0 : G) : ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) ≠ X0 ◇ (((x ◇ x) ◇ x) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef47 ef10 | exact superpose ef10 ef47
  subsumption ef862 ef47

theorem Equation4273_termDefinableFromFin_Equation873 : Law4273.TermDefinableFromFin Law873 := by
  intro G _ M hGL
  have h : Equation873 G := Law873.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_⟩
  · rw [@Law4273.models_iff]
    exact fun x y ↦ @aux873_4273 G _ M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩

/-- Equation 3269 `x ◇ x = y ◇ (x ◇ (x ◇ y))` is term-definable from equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))` over finite magmas, via the term
`x □ y := (x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y`. -/
private theorem aux898_3269 [Finite G] [Magma G] (h : Equation898 G) (x y : G) :
    (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x = (y ◇ ((y ◇ (y ◇
      ((x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)))) ◇ y)) ◇ ((x ◇ ((x ◇ (x ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef7 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ ((y ◇ (y ◇
      ((x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)))) ◇ y)) ◇ ((x ◇ ((x ◇ (x ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) := mod_symm nh
  have ef12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0) = X3 := superpose ef7 ef7
  have ef15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X2 := superpose ef8 ef8
  have ef17 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2)) = (X1 ◇ X0) ◇ X3 := superpose ef8 ef8
  have ef18 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0) = X2 := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef19 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ (X3 ◇ X2)) = X1 ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef20 (X0 X1 X2 X3 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = (X0 ◇ X3) ◇ (X3 ◇ X1) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef22 (X0 X1 X2 X3 : G) : X2 ◇ X1 = (X0 ◇ X3) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2)) := superpose ef9 ef9
  have ef26 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X2 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef27 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := superpose ef9 ef9
  have ef28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef84 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X3 := by
    first | exact superpose ef8 ef12 | exact superpose ef12 ef8
  have ef99 (X0 X1 X2 X3 : G) : X2 ◇ X3 = X0 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef12 ef9 | exact superpose ef9 ef12
  have ef193 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3 := by
    first | exact superpose ef15 ef8 | exact superpose ef8 ef15
  have ef237 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  have ef239 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ X0) = ((X0 ◇ X2) ◇ X4) ◇ X3 := by
    first | exact superpose ef15 ef17 | exact superpose ef17 ef15
  have ef247 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef15 ef17 | exact superpose ef17 ef15
  have ef266 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      ((y ◇ ((((x ◇ (x ◇ y)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇ x)) ◇
      y)) ◇ ((x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇
      y)) := by
    first | exact superpose ef17 ef10 | exact superpose ef10 ef17
  have ef329 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X0 ◇ X2) = ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X4) ◇ (X4 ◇ X3) := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef752 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ ((y ◇
      ((((x ◇ (x ◇ y)) ◇ X0) ◇ (X0 ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇ x)) ◇
      y)) ◇ ((x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇
      y)) := by
    first | exact superpose ef20 ef266 | exact superpose ef266 ef20
  have ef815 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇
      x))) ◇ (((y ◇
      ((((x ◇ (x ◇ y)) ◇ X0) ◇ (X0 ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇ x)) ◇
      y) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) := by
    first | exact superpose ef237 ef752 | exact superpose ef752 ef237
  have ef853 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇
      x))) ◇ (((y ◇
      ((x ◇ (X0 ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ X0)))) ◇ (x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))))) ◇
      y) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) := by
    first | exact superpose ef247 ef815 | exact superpose ef815 ef247
  have ef857 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇
      x))) ◇ (((y ◇
      ((x ◇ x) ◇ ((X0 ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ X0))) ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))))) ◇
      y) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) := by
    first | exact superpose ef237 ef853 | exact superpose ef853 ef237
  have ef859 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ (x ◇
      ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇
      (X0 ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ X0)))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) := by
    first | exact superpose ef247 ef857 | exact superpose ef857 ef247
  have ef861 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇
      ((X0 ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ X0))) ◇ y)) := by
    first | exact superpose ef237 ef859 | exact superpose ef859 ef237
  have ef863 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇
      ((X0 ◇ (x ◇ (y ◇ X0))) ◇ (x ◇ (x ◇ y)))) := by
    first | exact superpose ef247 ef861 | exact superpose ef861 ef247
  have ef865 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇
      ((((x ◇ y) ◇ x) ◇ x) ◇ y)) := by
    first | exact superpose ef239 ef863 | exact superpose ef863 ef239
  have ef867 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (((x ◇ y) ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) := by
    first | exact superpose ef237 ef865 | exact superpose ef865 ef237
  have ef869 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ (y ◇ y)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) := by
    first | exact superpose ef237 ef867 | exact superpose ef867 ef237
  have ef871 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ y) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇
      ((((x ◇ x) ◇ (y ◇ y)) ◇ x) ◇ y)) := by
    first | exact superpose ef237 ef869 | exact superpose ef869 ef237
  have ef873 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ y) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇
      (y ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef193 ef871 | exact superpose ef871 ef193
  have ef875 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ y) ◇ x)) ◇ y) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef237 ef873 | exact superpose ef873 ef237
  have ef877 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇
      (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ y) ◇ x)) ◇ y) ◇
      ((x ◇ x) ◇ (((x ◇ (x ◇ y)) ◇ x) ◇ (x ◇ x)))) := by
    first | exact superpose ef237 ef875 | exact superpose ef875 ef237
  have ef879 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ (y ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      ((((x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y)) ◇ ((x ◇ y) ◇ x)) ◇ y) ◇ ((x ◇ x) ◇ (x ◇ y))) := by
    first | exact superpose ef9 ef877 | exact superpose ef877 ef9
  have ef881 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ (y ◇ (x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x))) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ y))) := by
    first | exact superpose ef193 ef879 | exact superpose ef879 ef193
  have ef883 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x))) ◇
      ((x ◇ ((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ y))) := by
    first | exact superpose ef237 ef881 | exact superpose ef881 ef237
  have ef885 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x) ◇ (x ◇ y))) := by
    first | exact superpose ef237 ef883 | exact superpose ef883 ef237
  have ef887 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x)) ◇
      (((x ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ y))) ◇ x) ◇ (x ◇ y))) := by
    first | exact superpose ef237 ef885 | exact superpose ef885 ef237
  have ef889 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x)) ◇
      (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ x))) := by
    first | exact superpose ef329 ef887 | exact superpose ef887 ef329
  have ef891 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ x) ◇
      ((((x ◇ y) ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ x))) := by
    first | exact superpose ef237 ef889 | exact superpose ef889 ef237
  have ef1112 (X0 X1 X2 X3 X4 : G) :
      ((X3 ◇ X0) ◇ X4) ◇ X1 = (X2 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef17 ef22 | exact superpose ef22 ef17
  have ef1163 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ X4) ◇ (X4 ◇ (X2 ◇ X3)) := by
    first | exact superpose ef22 ef9 | exact superpose ef9 ef22
  have ef1646 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ (X4 ◇ (X5 ◇ ((X2 ◇ X3) ◇ X4)))) ◇ X5 := by
    first | exact superpose ef22 ef26 | exact superpose ef26 ef22
  have ef1805 (X0 X1 X2 X3 X5 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ ((X3 ◇ X5) ◇ X2)) ◇ X5 := by
    first | exact superpose ef17 ef1646 | exact superpose ef1646 ef17
  have ef1879 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ X4)) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) ◇ X5 := by
    first | exact superpose ef19 ef27 | exact superpose ef27 ef19
  have ef2037 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ X4)) = X4 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := by
    first | exact superpose ef1805 ef1879 | exact superpose ef1879 ef1805
  have ef2078 (X1 X2 X3 X4 : G) : X1 ◇ (X2 ◇ (X3 ◇ X4)) = X4 ◇ (X2 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef193 ef2037 | exact superpose ef2037 ef193
  have ef2232 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) = (((X3 ◇ X4) ◇ X2) ◇ X5) ◇ (X5 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef28 ef22 | exact superpose ef22 ef28
  have ef2244 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0) = ((X0 ◇ X2) ◇ X4) ◇ (X3 ◇ X1) := by
    first | exact superpose ef28 ef17 | exact superpose ef17 ef28
  have ef2259 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) := by
    first | exact superpose ef1163 ef2232 | exact superpose ef2232 ef1163
  have ef2969 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))) = (X4 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef84 ef99 | exact superpose ef99 ef84
  have ef3254 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ X3) ◇ X4 = (X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X1) ◇ (X0 ◇ X2))) := by
    first | exact superpose ef28 ef193 | exact superpose ef193 ef28
  have ef4747 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))) = X3 ◇ (X4 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ X5)) := by
    first | exact superpose ef193 ef2078 | exact superpose ef2078 ef193
  have ef4760 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ X3) ◇ (X4 ◇ ((X0 ◇ X2) ◇ X5)) = X5 ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := by
    first | exact superpose ef237 ef2078 | exact superpose ef2078 ef237
  have ef4992 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ (x ◇ (x ◇ y))) ◇ (((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ x) ◇
      ((((x ◇ y) ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ x))) := by
    first | exact superpose ef2078 ef891 | exact superpose ef891 ef2078
  have ef5041 (X0 X1 X2 X3 X4 X5 : G) :
      (X4 ◇ X3) ◇ (X5 ◇ (X1 ◇ (X2 ◇ X0))) = (X4 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    first | exact superpose ef2078 ef237 | exact superpose ef237 ef2078
  have ef5120 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇
      ((((x ◇ y) ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ x)))) := by
    first | exact superpose ef5041 ef4992 | exact superpose ef4992 ef5041
  have ef5298 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ y) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x))))) := by
    first | exact superpose ef5041 ef5120 | exact superpose ef5120 ef5041
  have ef5380 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ x) ◇ ((x ◇ x) ◇
      (((((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ x) ◇ y) ◇ (x ◇ (x ◇ y)))) := by
    first | exact superpose ef1112 ef5298 | exact superpose ef5298 ef1112
  have ef5412 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ x) ◇ ((x ◇ x) ◇
      (((((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ x) ◇ x) ◇ (y ◇ (x ◇ y)))) := by
    first | exact superpose ef2259 ef5380 | exact superpose ef5380 ef2259
  have ef5432 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ x) ◇ ((x ◇ x) ◇
      ((((x ◇ y) ◇ x) ◇ y) ◇ (x ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x))))) := by
    first | exact superpose ef2244 ef5412 | exact superpose ef5412 ef2244
  have ef5448 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ x) ◇ ((x ◇ x) ◇
      ((((x ◇ y) ◇ x) ◇ x) ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (((x ◇ y) ◇ x) ◇ x))))) := by
    first | exact superpose ef2259 ef5432 | exact superpose ef5432 ef2259
  have ef5464 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ x) ◇ ((x ◇ x) ◇
      ((((x ◇ y) ◇ x) ◇ x) ◇ (y ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ (((x ◇ (x ◇ y)) ◇ x) ◇ x))))) := by
    first | exact superpose ef4760 ef5448 | exact superpose ef5448 ef4760
  have ef5480 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ x) ◇ ((x ◇ x) ◇ ((((x ◇ (x ◇ y)) ◇ x) ◇ y) ◇ x)) := by
    first | exact superpose ef3254 ef5464 | exact superpose ef5464 ef3254
  have ef5496 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ x ◇ ((x ◇ x) ◇ ((((x ◇ (x ◇ y)) ◇ x) ◇ x) ◇ (y ◇ x))) := by
    first | exact superpose ef4760 ef5480 | exact superpose ef5480 ef4760
  have ef5512 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ x ◇ (x ◇ (x ◇ (y ◇ (x ◇ (((x ◇ (x ◇ y)) ◇ x) ◇ x))))) := by
    first | exact superpose ef2969 ef5496 | exact superpose ef5496 ef2969
  have ef5528 : (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ x ◇ (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) := by
    first | exact superpose ef4747 ef5512 | exact superpose ef5512 ef4747
  have ef6640 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ x ◇ (x ◇ (x ◇ (x ◇ (X0 ◇ (x ◇ (x ◇ X0)))))) := by
    first | exact superpose ef19 ef5528 | exact superpose ef5528 ef19
  have ef7549 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ x ◇ (x ◇ (x ◇ ((x ◇ ((x ◇ X0) ◇ x)) ◇ X0))) := by
    first | exact superpose ef99 ef6640 | exact superpose ef6640 ef99
  have ef8451 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ x ◇ (X0 ◇ (x ◇ ((x ◇ ((x ◇ X0) ◇ x)) ◇ x))) := by
    first | exact superpose ef2078 ef7549 | exact superpose ef7549 ef2078
  have ef9365 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((x ◇ ((x ◇ ((x ◇ X0) ◇ x)) ◇ x)) ◇ x) ◇ X0 := by
    first | exact superpose ef99 ef8451 | exact superpose ef8451 ef99
  have ef11264 : (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x := by
    first | exact superpose ef9 ef9365 | exact superpose ef9365 ef9
  exact absurd rfl ef11264

theorem Equation3269_termDefinableFromFin_Equation898 : Law3269.TermDefinableFromFin Law898 := by
  intro G _ M hGL
  have h : Equation898 G := Law898.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x (M.op (M.op x (M.op x y)) x)) y)⟩, ?_, ?_⟩
  · rw [@Law3269.models_iff]
    exact fun x y ↦ @aux898_3269 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 1))) (Term.var 0))) (Term.var 1)), rfl⟩

/-- Equation 3279 `x ◇ x = y ◇ (y ◇ (x ◇ y))` is term-definable from equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))` over finite magmas, via the term
`x □ y := (x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x`. -/
private theorem aux898_3279 [Finite G] [Magma G] (h : Equation898 G) (x y : G) :
    (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x = (y ◇ ((y ◇ (y ◇
      ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      y))) ◇ ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y))) ◇ y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef7 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (y ◇ ((y ◇ (y ◇
      ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      y))) ◇ ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y))) ◇ y := mod_symm nh
  have ef12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0) = X3 := superpose ef7 ef7
  have ef14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2 = X3 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X2 := superpose ef8 ef8
  have ef17 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2)) = (X1 ◇ X0) ◇ X3 := superpose ef8 ef8
  have ef19 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ (X3 ◇ X2)) = X1 ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef20 (X0 X1 X2 X3 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = (X0 ◇ X3) ◇ (X3 ◇ X1) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef22 (X0 X1 X2 X3 : G) : X2 ◇ X1 = (X0 ◇ X3) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2)) := superpose ef9 ef9
  have ef25 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ X0 = X3 := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef26 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X2 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef27 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := superpose ef9 ef9
  have ef28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef84 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X3 := by
    first | exact superpose ef8 ef12 | exact superpose ef12 ef8
  have ef99 (X0 X1 X2 X3 : G) : X2 ◇ X3 = X0 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef12 ef9 | exact superpose ef9 ef12
  have ef193 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3 := by
    first | exact superpose ef15 ef8 | exact superpose ef8 ef15
  have ef237 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  have ef239 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ X0) = ((X0 ◇ X2) ◇ X4) ◇ X3 := by
    first | exact superpose ef15 ef17 | exact superpose ef17 ef15
  have ef247 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef15 ef17 | exact superpose ef17 ef15
  have ef272 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X4 ◇ X3) := by
    first | exact superpose ef17 ef9 | exact superpose ef9 ef17
  have ef468 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ X0 = X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X4) ◇ X1)) := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef469 (X0 X1 X2 X3 X4 : G) :
      (X3 ◇ (X2 ◇ X4)) ◇ X0 = X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X1)) := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef540 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (X0 ◇ ((y ◇ (y ◇
      ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      y))) ◇ ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ X0))) ◇ y := by
    first | exact superpose ef19 ef10 | exact superpose ef10 ef19
  have ef577 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (X0 ◇ ((y ◇ (y ◇
      ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      y))) ◇ (y ◇ X0))) ◇ (y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇
      y)) ◇ x))) := by
    first | exact superpose ef247 ef540 | exact superpose ef540 ef247
  have ef604 (X0 X2 X3 X4 : G) : X2 ◇ X0 = (X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) ◇ X3 := by
    first | exact superpose ef469 ef468 | exact superpose ef468 ef469
  have ef625 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ ((x ◇
      ((x ◇ (x ◇ y)) ◇ y)) ◇ x)) ◇ (y ◇ (y ◇
      ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      y)))) ◇ y) ◇ y := by
    first | exact superpose ef239 ef577 | exact superpose ef577 ef239
  have ef635 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇ (((x ◇
      ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ (y ◇
      ((y ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇
      y)))) ◇ y) ◇ y := by
    first | exact superpose ef237 ef625 | exact superpose ef625 ef237
  have ef639 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇ (((x ◇
      ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ (y ◇
      ((x ◇ ((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ (y ◇ y))) ◇
      (x ◇ ((x ◇ (x ◇ y)) ◇ y)))))) ◇ y) ◇ y := by
    first | exact superpose ef247 ef635 | exact superpose ef635 ef247
  have ef643 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇ (((x ◇
      ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ (y ◇ ((x ◇ x) ◇
      (((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ (y ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ y)))))) ◇ y) ◇
      y := by
    first | exact superpose ef237 ef639 | exact superpose ef639 ef237
  have ef647 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇ (((x ◇
      ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ (y ◇ ((x ◇ x) ◇
      (((x ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ y))) ◇ ((x ◇ (x ◇ y)) ◇ y)))))) ◇ y) ◇
      y := by
    first | exact superpose ef247 ef643 | exact superpose ef643 ef247
  have ef651 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇ (((x ◇
      ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ (y ◇ ((x ◇ x) ◇
      (((x ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (x ◇ (x ◇ y))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ y)))))) ◇ y) ◇
      y := by
    first | exact superpose ef237 ef647 | exact superpose ef647 ef237
  have ef655 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇ (((x ◇
      ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ (y ◇ ((x ◇ x) ◇
      (((x ◇ x) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (x ◇ y))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ y)))))) ◇ y) ◇
      y := by
    first | exact superpose ef237 ef651 | exact superpose ef651 ef237
  have ef659 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇ (((x ◇
      ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ (y ◇ ((x ◇ x) ◇
      (((x ◇ x) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ y))) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (x ◇ y)) ◇ y)))))) ◇ y) ◇
      y := by
    first | exact superpose ef237 ef655 | exact superpose ef655 ef237
  have ef663 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ y))) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ y))))))) ◇ y) ◇
      y := by
    first | exact superpose ef193 ef659 | exact superpose ef659 ef193
  have ef667 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ ((x ◇ y) ◇ y))))))) ◇ y) ◇
      y := by
    first | exact superpose ef237 ef663 | exact superpose ef663 ef237
  have ef671 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ (((x ◇ (x ◇ y)) ◇ y) ◇ y))))))) ◇ y) ◇
      y := by
    first | exact superpose ef237 ef667 | exact superpose ef667 ef237
  have ef675 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ (x ◇ (y ◇ x)))))))) ◇ y) ◇ y := by
    first | exact superpose ef193 ef671 | exact superpose ef671 ef193
  have ef679 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ ((x ◇ y) ◇ (y ◇ x)))))))) ◇ y) ◇ y := by
    first | exact superpose ef237 ef675 | exact superpose ef675 ef237
  have ef683 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((y ◇ (y ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))) ◇ y) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))))) ◇ y) ◇ y := by
    first | exact superpose ef237 ef679 | exact superpose ef679 ef237
  have ef687 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((x ◇ (y ◇ (y ◇ y))) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ y))) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))))) ◇ y) ◇ y := by
    first | exact superpose ef247 ef683 | exact superpose ef683 ef247
  have ef691 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ y))) ◇
      (((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))))) ◇ y) ◇ y := by
    first | exact superpose ef237 ef687 | exact superpose ef687 ef237
  have ef695 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((x ◇ x) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x)) ◇
      (((y ◇ (y ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))))) ◇ y) ◇ y := by
    first | exact superpose ef237 ef691 | exact superpose ef691 ef237
  have ef698 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((((x ◇ x) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x)) ◇
      (((y ◇ (y ◇ y)) ◇ y) ◇ (((x ◇ (x ◇ y)) ◇ y) ◇
      ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))))) ◇ y) ◇ y := by
    first | exact superpose ef237 ef695 | exact superpose ef695 ef237
  have ef700 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇
      (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x))))) ◇ ((x ◇ (x ◇ y)) ◇
      y)) ◇ y := by
    first | exact superpose ef247 ef698 | exact superpose ef698 ef247
  have ef702 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y))) ◇
      ((((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x)))) ◇ y)) ◇ y := by
    first | exact superpose ef237 ef700 | exact superpose ef700 ef237
  have ef704 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y))) ◇
      ((((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ (y ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y)))) ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef247 ef702 | exact superpose ef702 ef247
  have ef706 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ ((((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y)))) ◇ (y ◇
      (((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y)))))) ◇
      x := by
    first | exact superpose ef247 ef704 | exact superpose ef704 ef247
  have ef708 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (x ◇ ((((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ y) ◇
      ((y ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇
      (((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y)))))) ◇
      x := by
    first | exact superpose ef237 ef706 | exact superpose ef706 ef237
  have ef710 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y))) ◇
      ((((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ (x ◇ x))) ◇ (y ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef247 ef708 | exact superpose ef708 ef247
  have ef712 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y))) ◇
      y) ◇ (((((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ (x ◇ x)) ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef237 ef710 | exact superpose ef710 ef237
  have ef714 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y))) ◇
      y) ◇ (((((x ◇ ((x ◇ (x ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ y) ◇ ((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef237 ef712 | exact superpose ef712 ef237
  have ef716 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y))) ◇
      y) ◇ ((((x ◇ (x ◇ y)) ◇ (x ◇ x)) ◇ y) ◇ ((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef193 ef714 | exact superpose ef714 ef193
  have ef718 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y))) ◇
      y) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef193 ef716 | exact superpose ef716 ef193
  have ef720 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x))))) ◇ (x ◇ (x ◇ y))) ◇
      y) ◇ ((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef237 ef718 | exact superpose ef718 ef237
  have ef722 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((y ◇ (x ◇ (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))))) ◇
      x) ◇ ((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef247 ef720 | exact superpose ef720 ef247
  have ef768 (X0 X1 X2 X3 X4 X5 : G) :
      ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X4) ◇ (X4 ◇ X5) = X0 ◇ (X3 ◇ X5) := by
    first | exact superpose ef14 ef20 | exact superpose ef20 ef14
  have ef856 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((y ◇ (x ◇ (y ◇ ((x ◇ x) ◇ (((x ◇ X0) ◇ (X0 ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))))))) ◇
      x) ◇ ((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef20 ef722 | exact superpose ef722 ef20
  have ef945 (X0 X1 X2 X3 X5 : G) :
      X0 ◇ (X3 ◇ X5) = (X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X5) := by
    first | exact superpose ef272 ef768 | exact superpose ef768 ef272
  have ef969 (X0 X1 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((y ◇
      (x ◇ (y ◇ ((x ◇ x) ◇ (((x ◇ X1) ◇ (X1 ◇ x)) ◇ ((y ◇ y) ◇ ((x ◇ X0) ◇ (X0 ◇ x)))))))) ◇ x) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef20 ef856 | exact superpose ef856 ef20
  have ef970 (X0 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((y ◇ (x ◇ (y ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ X0) ◇ (X0 ◇ x)))))))) ◇ x) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef945 ef969 | exact superpose ef969 ef945
  have ef1159 (X0 X1 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ ((y ◇ (x ◇ (y ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ (X1 ◇ (X0 ◇ (x ◇ X1)))) ◇ X0))))))) ◇ x) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef8 ef970 | exact superpose ef970 ef8
  have ef1264 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ X4) ◇ (X4 ◇ (X2 ◇ X3)) := by
    first | exact superpose ef22 ef9 | exact superpose ef9 ef22
  have ef1672 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X5))) = (((X0 ◇ X1) ◇ X2) ◇ X5) ◇ X3 := by
    first | exact superpose ef17 ef25 | exact superpose ef25 ef17
  have ef1864 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ (X4 ◇ (X5 ◇ ((X2 ◇ X3) ◇ X4)))) ◇ X5 := by
    first | exact superpose ef22 ef26 | exact superpose ef26 ef22
  have ef2030 (X0 X1 X2 X3 X5 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ ((X3 ◇ X5) ◇ X2)) ◇ X5 := by
    first | exact superpose ef17 ef1864 | exact superpose ef1864 ef17
  have ef2135 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = (((X0 ◇ X1) ◇ X2) ◇ ((X4 ◇ X5) ◇ X3)) ◇ X5 := by
    first | exact superpose ef17 ef27 | exact superpose ef27 ef17
  have ef2137 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ X4)) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) ◇ X5 := by
    first | exact superpose ef19 ef27 | exact superpose ef27 ef19
  have ef2306 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ X4)) = X4 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := by
    first | exact superpose ef2030 ef2137 | exact superpose ef2137 ef2030
  have ef2308 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef2030 ef2135 | exact superpose ef2135 ef2030
  have ef2348 (X1 X2 X3 X4 : G) : X1 ◇ (X2 ◇ (X3 ◇ X4)) = X4 ◇ (X2 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef193 ef2306 | exact superpose ef2306 ef193
  have ef2544 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) = (((X3 ◇ X4) ◇ X2) ◇ X5) ◇ (X5 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef28 ef22 | exact superpose ef22 ef28
  have ef2573 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) := by
    first | exact superpose ef1264 ef2544 | exact superpose ef2544 ef1264
  have ef3495 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))) = (X4 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef84 ef99 | exact superpose ef99 ef84
  have ef3517 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4 = X5 ◇ (((X5 ◇ X4) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := by
    first | exact superpose ef17 ef99 | exact superpose ef99 ef17
  have ef3929 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇
      X3 := superpose ef193 ef193
  have ef3935 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4) = ((X4 ◇ X0) ◇ X3) ◇ (X5 ◇ (X2 ◇ (X1 ◇ X5))) := by
    first | exact superpose ef15 ef193 | exact superpose ef193 ef15
  have ef4641 (X0 X1 X2 X3 X4 X5 : G) :
      (X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X5) = (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ X4) ◇ (X3 ◇ X5) := by
    first | exact superpose ef193 ef237 | exact superpose ef237 ef193
  have ef4654 (X0 X1 X2 X3 X4 X5 : G) :
      ((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5) = ((X0 ◇ X2) ◇ X4) ◇
      ((X1 ◇ X3) ◇ X5) := superpose ef237 ef237
  have ef4657 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ X5) ◇ ((X0 ◇ X1) ◇ X2) = (X3 ◇ X4) ◇ (X5 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X4))) := by
    first | exact superpose ef17 ef237 | exact superpose ef237 ef17
  have ef5626 (X0 X1 X2 X3 X4 X5 : G) :
      ((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4 = (X5 ◇ (X0 ◇ (X4 ◇ X5))) ◇ ((X2 ◇ X3) ◇ X1) := by
    first | exact superpose ef28 ef604 | exact superpose ef604 ef28
  have ef5749 (X0 X1 X2 X3 X4 X5 : G) :
      (X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2))) ◇ (X4 ◇ X5) = ((X5 ◇ (X0 ◇ X1)) ◇ X4) ◇ X3 := by
    first | exact superpose ef604 ef193 | exact superpose ef193 ef604
  have ef5841 (X0 X1 X3 X4 X5 : G) :
      ((X5 ◇ (X0 ◇ X1)) ◇ X4) ◇ X3 = ((X5 ◇ (X0 ◇ X3)) ◇ X4) ◇ X1 := by
    first | exact superpose ef239 ef5749 | exact superpose ef5749 ef239
  have ef5916 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4 = ((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4 := by
    first | exact superpose ef239 ef5626 | exact superpose ef5626 ef239
  have ef6243 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X4 ◇ (X3 ◇ X5)) = X5 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2)) := by
    first | exact superpose ef17 ef2348 | exact superpose ef2348 ef17
  have ef6248 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ (X2 ◇ X0)) ◇ (X4 ◇ (X3 ◇ X5)) = X5 ◇
      (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose ef2348 ef2348
  have ef6624 (X0 X1 X2 X3 X4 X5 : G) :
      (X4 ◇ X3) ◇ (X5 ◇ (X1 ◇ (X2 ◇ X0))) = (X4 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    first | exact superpose ef2348 ef237 | exact superpose ef237 ef2348
  have ef6629 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((y ◇ (x ◇ (y ◇
      (x ◇ (x ◇ ((y ◇ y) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))))))) ◇
      x) ◇ ((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef2348 ef1159 | exact superpose ef1159 ef2348
  have ef6672 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (x ◇ (x ◇ y))) ◇
      (x ◇ (x ◇ x))) ◇ (y ◇
      (x ◇ (x ◇ ((y ◇ y) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))))) := by
    first | exact superpose ef3929 ef6629 | exact superpose ef6629 ef3929
  have ef6940 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y) ◇
      (((x ◇ (x ◇ y)) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ ((y ◇ y) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))))) := by
    first | exact superpose ef4654 ef6672 | exact superpose ef6672 ef4654
  have ef7095 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y) ◇
      (((x ◇ (x ◇ y)) ◇ x) ◇ ((x ◇ x) ◇
      (x ◇ ((y ◇ y) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))))) := by
    first | exact superpose ef2573 ef6940 | exact superpose ef6940 ef2573
  have ef7197 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ (((x ◇ (((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y)) ◇ (x ◇ (x ◇ y))) ◇
      ((y ◇ y) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))) ◇ x := by
    first | exact superpose ef1672 ef7095 | exact superpose ef7095 ef1672
  have ef7283 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ (((x ◇ (((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇
      ((x ◇ (x ◇ y)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))) ◇ x := by
    first | exact superpose ef5916 ef7197 | exact superpose ef7197 ef5916
  have ef7359 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      x ≠ (((x ◇ (((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y)) ◇ (y ◇ x)) ◇
      ((x ◇ (x ◇ y)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))) ◇ y := by
    first | exact superpose ef5841 ef7283 | exact superpose ef7283 ef5841
  have ef7435 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ (((x ◇ y) ◇ (x ◇ (x ◇ y))) ◇
      (((((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ x) ◇
      (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))) ◇ y := by
    first | exact superpose ef4654 ef7359 | exact superpose ef7359 ef4654
  have ef7511 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ ((y ◇ (x ◇ y)) ◇ x) ◇
      ((((((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ x) ◇
      (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3)))))))) ◇ (x ◇ y)) := by
    first | exact superpose ef3929 ef7435 | exact superpose ef7435 ef3929
  have ef7587 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((y ◇ (x ◇ y)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ x) ◇
      (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (x ◇ X3))))))))))) := by
    first | exact superpose ef3495 ef7511 | exact superpose ef7511 ef3495
  have ef7663 (X0 X1 X2 X3 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((y ◇ (x ◇ y)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ x) ◇
      (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ (X3 ◇ ((X1 ◇ x) ◇ ((X2 ◇ X0) ◇ X3))))))))))) := by
    first | exact superpose ef2308 ef7587 | exact superpose ef7587 ef2308
  have ef7739 (X0 X1 X2 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((y ◇ (x ◇ y)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ x) ◇
      (X0 ◇ (X1 ◇ (X2 ◇ (x ◇ ((X0 ◇ (X1 ◇ x)) ◇ X2))))))))) := by
    first | exact superpose ef17 ef7663 | exact superpose ef7663 ef17
  have ef7815 (X0 X1 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((y ◇ (x ◇ y)) ◇
      (((((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ y) ◇ x) ◇
      (X0 ◇ (X1 ◇ (((X1 ◇ x) ◇ x) ◇ X0))))))) := by
    first | exact superpose ef17 ef7739 | exact superpose ef7739 ef17
  have ef7889 (X1 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((y ◇ (x ◇ y)) ◇
      ((((X1 ◇ x) ◇ x) ◇ (y ◇ X1)) ◇ (x ◇ ((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x)))))) := by
    first | exact superpose ef3935 ef7815 | exact superpose ef7815 ef3935
  have ef7963 (X1 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((y ◇ x) ◇ ((x ◇ y) ◇
      (x ◇ ((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((X1 ◇ x) ◇ x) ◇ (y ◇ X1)))))))) := by
    first | exact superpose ef6624 ef7889 | exact superpose ef7889 ef6624
  have ef8037 (X1 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((y ◇ x) ◇ ((x ◇ x) ◇
      (y ◇ ((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((X1 ◇ x) ◇ x) ◇ (y ◇ X1)))))))) := by
    first | exact superpose ef2573 ef7963 | exact superpose ef7963 ef2573
  have ef8107 (X1 : G) :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((y ◇ x) ◇
      ((x ◇ x) ◇ (y ◇ (X1 ◇ (((X1 ◇ x) ◇ x) ◇ (((y ◇ y) ◇ ((x ◇ x) ◇ x)) ◇ y)))))))) := by
    first | exact superpose ef6243 ef8037 | exact superpose ef8037 ef6243
  have ef8177 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇
      (x ◇ (x ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ x)) ◇ x)))))) := by
    first | exact superpose ef3517 ef8107 | exact superpose ef8107 ef3517
  have ef8247 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇
      (x ◇ (x ◇ ((y ◇ (x ◇ x)) ◇ ((((y ◇ (y ◇ y)) ◇ x) ◇ y) ◇ ((x ◇ x) ◇ x))))) := by
    first | exact superpose ef4657 ef8177 | exact superpose ef8177 ef4657
  have ef8317 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇
      (x ◇ (x ◇ (x ◇ ((((y ◇ (y ◇ y)) ◇ x) ◇ y) ◇ (x ◇ (y ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef6248 ef8247 | exact superpose ef8247 ef6248
  have ef8387 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇
      (x ◇ (x ◇ (x ◇ ((((y ◇ (y ◇ y)) ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef2573 ef8317 | exact superpose ef8317 ef2573
  have ef8455 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇
      (x ◇ (x ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ (x ◇ (y ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef4641 ef8387 | exact superpose ef8387 ef4641
  have ef8517 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇
      (x ◇ (x ◇ (x ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (y ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef2573 ef8455 | exact superpose ef8455 ef2573
  have ef8573 :
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (x ◇ (x ◇ ((((x ◇ x) ◇ y) ◇ (x ◇ (x ◇ x))) ◇ x))) := by
    first | exact superpose ef1672 ef8517 | exact superpose ef8517 ef1672
  have ef8627 : (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x ≠ y ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ y)) := by
    first | exact superpose ef17 ef8573 | exact superpose ef8573 ef17
  subsumption ef8627 ef17

theorem Equation3279_termDefinableFromFin_Equation898 : Law3279.TermDefinableFromFin Law898 := by
  intro G _ M hGL
  have h : Equation898 G := Law898.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x (M.op (M.op x (M.op x y)) y)) x)⟩, ?_, ?_⟩
  · rw [@Law3279.models_iff]
    exact fun x y ↦ @aux898_3279 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 1))) (Term.var 1))) (Term.var 0)), rfl⟩

/-- Equation 3475 `x ◇ x = y ◇ ((x ◇ y) ◇ y)` is term-definable from equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))` over finite magmas, via the term
`x □ y := (x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)`. -/
private theorem aux898_3475 [Finite G] [Magma G] (h : Equation898 G) (x y : G) :
    (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) = (y ◇ ((y ◇ y) ◇ y)) ◇ (((((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)) ◇
      ((((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y))) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)))) ◇ (y ◇ y)) ◇ ((((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)) ◇
      ((((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y))) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)))) ◇ (y ◇ y))) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef7 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (y ◇ ((y ◇ y) ◇ y)) ◇ (((((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)) ◇
      ((((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y))) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)))) ◇ (y ◇ y)) ◇ ((((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)) ◇
      ((((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y))) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ y)))) ◇ (y ◇ y))) := mod_symm nh
  have ef12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0) = X3 := superpose ef7 ef7
  have ef15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X2 := superpose ef8 ef8
  have ef17 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2)) = (X1 ◇ X0) ◇ X3 := superpose ef8 ef8
  have ef19 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ (X3 ◇ X2)) = X1 ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef20 (X0 X1 X2 X3 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = (X0 ◇ X3) ◇ (X3 ◇ X1) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef22 (X0 X1 X2 X3 : G) : X2 ◇ X1 = (X0 ◇ X3) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2)) := superpose ef9 ef9
  have ef25 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ X0 = X3 := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef26 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X2 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef27 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := superpose ef9 ef9
  have ef28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef29 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef84 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X3 := by
    first | exact superpose ef8 ef12 | exact superpose ef12 ef8
  have ef91 (X0 X1 X2 X3 : G) : X2 ◇ X3 = X0 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef12 ef9 | exact superpose ef9 ef12
  have ef196 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3 := by
    first | exact superpose ef15 ef8 | exact superpose ef8 ef15
  have ef237 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  have ef247 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef15 ef17 | exact superpose ef17 ef15
  have ef265 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X4 ◇ X3) := by
    first | exact superpose ef17 ef9 | exact superpose ef9 ef17
  have ef435 (X0 X1 X2 X3 X4 : G) :
      (X3 ◇ (X2 ◇ X4)) ◇ X0 = X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X1)) := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef640 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ X4) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X5))) = (X3 ◇ X5) ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef1031 (X0 X1 X2 X3 X4 : G) :
      ((X3 ◇ X0) ◇ X4) ◇ X1 = (X2 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef17 ef22 | exact superpose ef22 ef17
  have ef1033 (X0 X1 X2 X3 X4 : G) :
      (X3 ◇ X4) ◇ X1 = (X2 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := by
    first | exact superpose ef19 ef22 | exact superpose ef22 ef19
  have ef1086 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ X4) ◇ (X4 ◇ (X2 ◇ X3)) := by
    first | exact superpose ef22 ef9 | exact superpose ef9 ef22
  have ef1385 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X5))) = (((X0 ◇ X1) ◇ X2) ◇ X5) ◇ X3 := by
    first | exact superpose ef17 ef25 | exact superpose ef25 ef17
  have ef1559 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ (X4 ◇ (X5 ◇ ((X2 ◇ X3) ◇ X4)))) ◇ X5 := by
    first | exact superpose ef22 ef26 | exact superpose ef26 ef22
  have ef1718 (X0 X1 X2 X3 X5 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ ((X3 ◇ X5) ◇ X2)) ◇ X5 := by
    first | exact superpose ef17 ef1559 | exact superpose ef1559 ef17
  have ef1790 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = (((X0 ◇ X1) ◇ X2) ◇ ((X4 ◇ X5) ◇ X3)) ◇ X5 := by
    first | exact superpose ef17 ef27 | exact superpose ef27 ef17
  have ef1952 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef1718 ef1790 | exact superpose ef1790 ef1718
  have ef2110 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ X2) ◇ X4) ◇ (X3 ◇ X1) = ((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0) := by
    first | exact superpose ef28 ef17 | exact superpose ef17 ef28
  have ef2148 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ (X4 ◇ X5) = X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X5) := by
    first | exact superpose ef28 ef20 | exact superpose ef20 ef28
  have ef2152 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) = (((X3 ◇ X4) ◇ X2) ◇ X5) ◇ (X5 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef28 ef22 | exact superpose ef22 ef28
  have ef2166 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) := by
    first | exact superpose ef1086 ef2152 | exact superpose ef2152 ef1086
  have ef2169 (X0 X1 X2 X3 X5 : G) :
      X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X5) = X2 ◇ (((X0 ◇ X3) ◇ X1) ◇ X5) := by
    first | exact superpose ef265 ef2148 | exact superpose ef2148 ef265
  have ef2871 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))) = (X4 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef84 ef91 | exact superpose ef91 ef84
  have ef2893 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4 = X5 ◇ (((X5 ◇ X4) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := by
    first | exact superpose ef17 ef91 | exact superpose ef91 ef17
  have ef3134 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇
      X3 := superpose ef196 ef196
  have ef3139 (X0 X1 X2 X3 X4 X5 : G) :
      ((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X5) = ((X5 ◇ X0) ◇ X4) ◇ ((X2 ◇ X3) ◇ X1) := by
    first | exact superpose ef28 ef196 | exact superpose ef196 ef28
  have ef3156 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ X3) ◇ X4 = (X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X1) ◇ (X0 ◇ X2))) := by
    first | exact superpose ef28 ef196 | exact superpose ef196 ef28
  have ef3167 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X4 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X5))) ◇ X1)) = ((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇
      X5 := superpose ef196 ef196
  have ef3279 (X0 X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X3))) ◇ X1 = (X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5) := by
    first | exact superpose ef196 ef29 | exact superpose ef29 ef196
  have ef3481 (X0 X1 X2 X3 X4 X5 : G) :
      ((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5) = ((X0 ◇ X2) ◇ X4) ◇
      ((X1 ◇ X3) ◇ X5) := superpose ef237 ef237
  have ef3484 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ X5) ◇ ((X0 ◇ X1) ◇ X2) = (X3 ◇ X4) ◇ (X5 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X4))) := by
    first | exact superpose ef17 ef237 | exact superpose ef237 ef17
  have ef3660 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (y ◇ ((y ◇ y) ◇ y)) ◇ (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (y ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (y ◇ y))) := by
    first | exact superpose ef237 ef10 | exact superpose ef10 ef237
  have ef3703 (X0 X1 X2 X3 X4 X5 : G) :
      ((X1 ◇ X3) ◇ X5) ◇ (X0 ◇ X2) = X4 ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) := by
    first | exact superpose ef237 ef17 | exact superpose ef17 ef237
  have ef3751 (X0 X1 X2 X3 X5 : G) :
      ((X1 ◇ X3) ◇ X5) ◇ (X0 ◇ X2) = ((X2 ◇ X3) ◇ X5) ◇ (X0 ◇ X1) := by
    first | exact superpose ef17 ef3703 | exact superpose ef3703 ef17
  have ef3778 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (y ◇ y)) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ y))))) ◇ ((y ◇ y) ◇ y)) ◇ y := by
    first | exact superpose ef1031 ef3660 | exact superpose ef3660 ef1031
  have ef3904 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ y) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (y ◇ y))) := by
    first | exact superpose ef1718 ef3778 | exact superpose ef3778 ef1718
  have ef3946 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((((y ◇ y) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ y) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) := by
    first | exact superpose ef3751 ef3904 | exact superpose ef3904 ef3751
  have ef3963 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((((y ◇ y) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))))) ◇ ((x ◇ (x ◇ y)) ◇ (x ◇ x))) := by
    first | exact superpose ef3484 ef3946 | exact superpose ef3946 ef3484
  have ef3969 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((((y ◇ y) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (x ◇ x))) := by
    first | exact superpose ef2166 ef3963 | exact superpose ef3963 ef2166
  have ef3975 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((((x ◇ x) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ (y ◇ y))) := by
    first | exact superpose ef3751 ef3969 | exact superpose ef3969 ef3751
  have ef3981 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ (y ◇ (((x ◇ x) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))))))) := by
    first | exact superpose ef2871 ef3975 | exact superpose ef3975 ef2871
  have ef3987 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (y ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))))))) := by
    first | exact superpose ef2166 ef3981 | exact superpose ef3981 ef2166
  have ef3993 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (y ◇ ((((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      (x ◇ x))) ◇ (x ◇ y)) ◇ (((x ◇ x) ◇ x) ◇ y))) := by
    first | exact superpose ef3167 ef3987 | exact superpose ef3987 ef3167
  have ef3999 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((y ◇ (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      (x ◇ x))) ◇ ((x ◇ x) ◇ x))) ◇ x) := by
    first | exact superpose ef435 ef3993 | exact superpose ef3993 ef435
  have ef4005 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((x ◇ (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      (x ◇ x))) ◇ (x ◇ y))) ◇ (x ◇ x)) := by
    first | exact superpose ef247 ef3999 | exact superpose ef3999 ef247
  have ef4011 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ x) ◇ ((((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      (x ◇ x))) ◇ (x ◇ y)) ◇ y)) := by
    first | exact superpose ef1952 ef4005 | exact superpose ef4005 ef1952
  have ef4017 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ x) ◇ (((x ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      y)) ◇ x) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ y)))))) := by
    first | exact superpose ef3134 ef4011 | exact superpose ef4011 ef3134
  have ef4023 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ ((((x ◇ x) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      y)) ◇ x) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ y)))))) := by
    first | exact superpose ef2169 ef4017 | exact superpose ef4017 ef2169
  have ef4029 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (x ◇ (((x ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ y)) ◇
      (((x ◇ x) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ y)) ◇
      (x ◇ y)))))) := by
    first | exact superpose ef2871 ef4023 | exact superpose ef4023 ef2871
  have ef4035 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (((x ◇ y) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ y) ◇ (((x ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ y)) ◇
      (((x ◇ x) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ y)) ◇
      (x ◇ y)))))) := by
    first | exact superpose ef2166 ef4029 | exact superpose ef4029 ef2166
  have ef4041 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      (((x ◇ x) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ y)) ◇ (x ◇ y))) ◇
      ((x ◇ x) ◇ x)) ◇ x)) ◇ y) := by
    first | exact superpose ef2893 ef4035 | exact superpose ef4035 ef2893
  have ef4047 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ (x ◇
      (((((x ◇ x) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ y)) ◇ (x ◇ y)) ◇
      x) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))))) ◇ y) := by
    first | exact superpose ef1718 ef4041 | exact superpose ef4041 ef1718
  have ef4053 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (x ◇ (y ◇ y))) ◇
      ((((x ◇ x) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      y)) ◇ (x ◇ y)) ◇ x)) := by
    first | exact superpose ef247 ef4047 | exact superpose ef4047 ef247
  have ef4059 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((y ◇ y) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇
      y)) ◇ (x ◇ y)))) ◇ x := by
    first | exact superpose ef435 ef4053 | exact superpose ef4053 ef435
  have ef4065 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((x ◇ y) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (x ◇ (y ◇
      y)))) ◇ ((x ◇ x) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ y)) := by
    first | exact superpose ef247 ef4059 | exact superpose ef4059 ef247
  have ef4071 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((x ◇ x) ◇ (y ◇ x)) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (x ◇
      (y ◇ y))) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ y)) := by
    first | exact superpose ef3481 ef4065 | exact superpose ef4065 ef3481
  have ef4077 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((y ◇ x) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) ◇ ((x ◇ x) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇
      (x ◇ (y ◇ y)))))) := by
    first | exact superpose ef2871 ef4071 | exact superpose ef4071 ef2871
  have ef4083 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((y ◇ x) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (x ◇ x)) ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (x ◇ (y ◇ y)))))) := by
    first | exact superpose ef2166 ef4077 | exact superpose ef4077 ef2166
  have ef4089 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇
      (((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ (x ◇ (y ◇ y))) ◇
      (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) := by
    first | exact superpose ef1385 ef4083 | exact superpose ef4083 ef1385
  have ef4095 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ x) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ x)))) := by
    first | exact superpose ef3139 ef4089 | exact superpose ef4089 ef3139
  have ef4101 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇
      (((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y))) ◇
      (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) := by
    first | exact superpose ef2110 ef4095 | exact superpose ef4095 ef2110
  have ef4107 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇
      (((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) := by
    first | exact superpose ef2166 ef4101 | exact superpose ef4101 ef2166
  have ef4113 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((y ◇ (x ◇ x)) ◇ (((x ◇ y) ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇ x)) := by
    first | exact superpose ef3279 ef4107 | exact superpose ef4107 ef3279
  have ef4119 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ ((x ◇ y) ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ x)))) ◇ ((x ◇ x) ◇ y)) := by
    first | exact superpose ef1952 ef4113 | exact superpose ef4113 ef1952
  have ef4125 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ (x ◇ x)) ◇ (((x ◇ y) ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇ y)) := by
    first | exact superpose ef2166 ef4119 | exact superpose ef4119 ef2166
  have ef4131 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ ((((y ◇ (x ◇ x)) ◇ y) ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇ y)) := by
    first | exact superpose ef2169 ef4125 | exact superpose ef4125 ef2169
  have ef4137 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ ((x ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (y ◇ ((y ◇ (x ◇ x)) ◇ y)))) ◇ ((x ◇ x) ◇ (y ◇ x)))) := by
    first | exact superpose ef247 ef4131 | exact superpose ef4131 ef247
  have ef4143 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇
      ((((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (y ◇ ((y ◇ (x ◇ x)) ◇ y))) ◇ (y ◇ x)))) := by
    first | exact superpose ef2166 ef4137 | exact superpose ef4137 ef2166
  have ef4149 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ (y ◇ ((y ◇ (x ◇ x)) ◇ y)))))))) := by
    first | exact superpose ef2871 ef4143 | exact superpose ef4143 ef2871
  have ef4155 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ y) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((y ◇ (x ◇ x)) ◇ y)))))))) := by
    first | exact superpose ef2166 ef4149 | exact superpose ef4149 ef2166
  have ef4161 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇
      (((((y ◇ (x ◇ x)) ◇ y) ◇ (y ◇ y)) ◇ y) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))))))))) := by
    first | exact superpose ef3751 ef4155 | exact superpose ef4155 ef3751
  have ef4167 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇
      (((((y ◇ (x ◇ x)) ◇ y) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ ((x ◇ (x ◇ y)) ◇ (x ◇ x)))))))) := by
    first | exact superpose ef3484 ef4161 | exact superpose ef4161 ef3484
  have ef4173 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇
      (((((y ◇ (x ◇ x)) ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (x ◇ x)))))))) := by
    first | exact superpose ef2166 ef4167 | exact superpose ef4167 ef2166
  have ef4179 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇
      ((((x ◇ x) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((y ◇ (x ◇ x)) ◇ y)))))))) := by
    first | exact superpose ef3751 ef4173 | exact superpose ef4173 ef3751
  have ef4185 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇
      (y ◇ ((x ◇ (x ◇ y)) ◇ ((y ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))))))))))) := by
    first | exact superpose ef2871 ef4179 | exact superpose ef4179 ef2871
  have ef4191 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇
      (y ◇ ((((((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ y) ◇ (x ◇ y)) ◇ x))))))) := by
    first | exact superpose ef1031 ef4185 | exact superpose ef4185 ef1031
  have ef4197 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇
      (y ◇ (((x ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ y)))))) := by
    first | exact superpose ef17 ef4191 | exact superpose ef4191 ef17
  have ef4203 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇
      (x ◇ (((y ◇ y) ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ y)))))) := by
    first | exact superpose ef2169 ef4197 | exact superpose ef4197 ef2169
  have ef4209 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (x ◇ (x ◇
      ((x ◇ y) ◇ ((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y)))))) := by
    first | exact superpose ef640 ef4203 | exact superpose ef4203 ef640
  have ef4215 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (x ◇ (x ◇ ((y ◇ (((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ y))) ◇ x))) := by
    first | exact superpose ef3156 ef4209 | exact superpose ef4209 ef3156
  have ef4221 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (((((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ y)) ◇ x) ◇ y) := by
    first | exact superpose ef17 ef4215 | exact superpose ef4215 ef17
  have ef4227 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ y) ◇ (x ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) := by
    first | exact superpose ef196 ef4221 | exact superpose ef4221 ef196
  have ef4233 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ x) ◇ (y ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)))) := by
    first | exact superpose ef2166 ef4227 | exact superpose ef4227 ef2166
  have ef4239 : (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef1033 ef4233 | exact superpose ef4233 ef1033
  have ef4245 : x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x) ≠ (x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef237 ef4239 | exact superpose ef4239 ef237
  subsumption ef4245 ef2169

theorem Equation3475_termDefinableFromFin_Equation898 : Law3475.TermDefinableFromFin Law898 := by
  intro G _ M hGL
  have h : Equation898 G := Law898.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x (M.op (M.op x x) x)) (M.op y y))⟩, ?_, ?_⟩
  · rw [@Law3475.models_iff]
    exact fun x y ↦ @aux898_3475 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))) (tm (Term.var 1) (Term.var 1))), rfl⟩

/-- Equation 3482 `x ◇ x = y ◇ ((y ◇ x) ◇ y)` is term-definable from equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))` over finite magmas, via the term
`x □ y := (x ◇ ((x ◇ x) ◇ y)) ◇ (x ◇ y)`. -/
private theorem aux898_3482 [Finite G] [Magma G] (h : Equation898 G) (x y : G) :
    (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) = (y ◇ ((y ◇ y) ◇ ((((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x))) ◇ y)) ◇
      (((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇ y)))) ◇ (y ◇ ((((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x))) ◇ y)) ◇
      (((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇ y))) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef7 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (y ◇ ((y ◇ y) ◇ ((((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x))) ◇ y)) ◇
      (((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇ y)))) ◇ (y ◇ ((((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x))) ◇ y)) ◇
      (((y ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ x)) ◇ y))) := mod_symm nh
  have ef12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0) = X3 := superpose ef7 ef7
  have ef15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X2 := superpose ef8 ef8
  have ef17 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2)) = (X1 ◇ X0) ◇ X3 := superpose ef8 ef8
  have ef19 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ (X3 ◇ X2)) = X1 ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef20 (X0 X1 X2 X3 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = (X0 ◇ X3) ◇ (X3 ◇ X1) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef21 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X2 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef22 (X0 X1 X2 X3 : G) : X2 ◇ X1 = (X0 ◇ X3) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2)) := superpose ef9 ef9
  have ef25 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ X0 = X3 := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef26 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X2 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef27 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := superpose ef9 ef9
  have ef28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef29 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef84 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X0 = X3 := by
    first | exact superpose ef8 ef12 | exact superpose ef12 ef8
  have ef91 (X0 X1 X2 X3 : G) : X2 ◇ X3 = X0 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef12 ef9 | exact superpose ef9 ef12
  have ef196 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3 := by
    first | exact superpose ef15 ef8 | exact superpose ef8 ef15
  have ef237 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  have ef247 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef15 ef17 | exact superpose ef17 ef15
  have ef265 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X4 ◇ X3) := by
    first | exact superpose ef17 ef9 | exact superpose ef9 ef17
  have ef895 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ X4) ◇ X3 = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ X0) := by
    first | exact superpose ef21 ef17 | exact superpose ef17 ef21
  have ef1036 (X0 X1 X2 X3 X4 : G) :
      ((X3 ◇ X0) ◇ X4) ◇ X1 = (X2 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef17 ef22 | exact superpose ef22 ef17
  have ef1091 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ X4) ◇ (X4 ◇ (X2 ◇ X3)) := by
    first | exact superpose ef22 ef9 | exact superpose ef9 ef22
  have ef1390 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X5))) = (((X0 ◇ X1) ◇ X2) ◇ X5) ◇ X3 := by
    first | exact superpose ef17 ef25 | exact superpose ef25 ef17
  have ef1564 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ (X4 ◇ (X5 ◇ ((X2 ◇ X3) ◇ X4)))) ◇ X5 := by
    first | exact superpose ef22 ef26 | exact superpose ef26 ef22
  have ef1723 (X0 X1 X2 X3 X5 : G) :
      X3 ◇ ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ ((X3 ◇ X5) ◇ X2)) ◇ X5 := by
    first | exact superpose ef17 ef1564 | exact superpose ef1564 ef17
  have ef1795 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = (((X0 ◇ X1) ◇ X2) ◇ ((X4 ◇ X5) ◇ X3)) ◇ X5 := by
    first | exact superpose ef17 ef27 | exact superpose ef27 ef17
  have ef1797 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ X4)) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) ◇ X5 := by
    first | exact superpose ef19 ef27 | exact superpose ef27 ef19
  have ef1955 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ X4)) = X4 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := by
    first | exact superpose ef1723 ef1797 | exact superpose ef1797 ef1723
  have ef1957 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef1723 ef1795 | exact superpose ef1795 ef1723
  have ef1996 (X1 X2 X3 X4 : G) : X1 ◇ (X2 ◇ (X3 ◇ X4)) = X4 ◇ (X2 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef196 ef1955 | exact superpose ef1955 ef196
  have ef2115 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ X2) ◇ X4) ◇ (X3 ◇ X1) = ((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0) := by
    first | exact superpose ef28 ef17 | exact superpose ef17 ef28
  have ef2153 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ (X4 ◇ X5) = X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X5) := by
    first | exact superpose ef28 ef20 | exact superpose ef20 ef28
  have ef2157 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) = (((X3 ◇ X4) ◇ X2) ◇ X5) ◇ (X5 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef28 ef22 | exact superpose ef22 ef28
  have ef2171 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) = X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) := by
    first | exact superpose ef1091 ef2157 | exact superpose ef2157 ef1091
  have ef2174 (X0 X1 X2 X3 X5 : G) :
      X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X5) = X2 ◇ (((X0 ◇ X3) ◇ X1) ◇ X5) := by
    first | exact superpose ef265 ef2153 | exact superpose ef2153 ef265
  have ef2876 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))) = (X4 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef84 ef91 | exact superpose ef91 ef84
  have ef2898 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4 = X5 ◇ (((X5 ◇ X4) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := by
    first | exact superpose ef17 ef91 | exact superpose ef91 ef17
  have ef3139 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇
      X3 := superpose ef196 ef196
  have ef3144 (X0 X1 X2 X3 X4 X5 : G) :
      ((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X5) = ((X5 ◇ X0) ◇ X4) ◇ ((X2 ◇ X3) ◇ X1) := by
    first | exact superpose ef28 ef196 | exact superpose ef196 ef28
  have ef3145 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4) = ((X4 ◇ X0) ◇ X3) ◇ (X5 ◇ (X2 ◇ (X1 ◇ X5))) := by
    first | exact superpose ef15 ef196 | exact superpose ef196 ef15
  have ef3172 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X4 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X5))) ◇ X1)) = ((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇
      X5 := superpose ef196 ef196
  have ef3284 (X0 X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X3))) ◇ X1 = (X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5) := by
    first | exact superpose ef196 ef29 | exact superpose ef29 ef196
  have ef3489 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ X5) ◇ ((X0 ◇ X1) ◇ X2) = (X3 ◇ X4) ◇ (X5 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X4))) := by
    first | exact superpose ef17 ef237 | exact superpose ef237 ef17
  have ef3671 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (y ◇ ((y ◇ y) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y)))) ◇ (y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇
      (((y ◇ y) ◇ x) ◇ x)) ◇ y))) := by
    first | exact superpose ef237 ef10 | exact superpose ef10 ef237
  have ef3716 (X0 X1 X2 X3 X4 X5 : G) :
      ((X1 ◇ X3) ◇ X5) ◇ (X0 ◇ X2) = X4 ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) := by
    first | exact superpose ef237 ef17 | exact superpose ef17 ef237
  have ef3764 (X0 X1 X2 X3 X5 : G) :
      ((X1 ◇ X3) ◇ X5) ◇ (X0 ◇ X2) = ((X2 ◇ X3) ◇ X5) ◇ (X0 ◇ X1) := by
    first | exact superpose ef17 ef3716 | exact superpose ef3716 ef17
  have ef3793 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y) ◇ ((y ◇ y) ◇ (((y ◇
      y) ◇ x) ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇
      (((y ◇ y) ◇ x) ◇ x))) ◇ y)) := by
    first | exact superpose ef3284 ef3671 | exact superpose ef3671 ef3284
  have ef3927 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (x ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ ((((y ◇ y) ◇
      ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇
      (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ x) := by
    first | exact superpose ef3284 ef3793 | exact superpose ef3793 ef3284
  have ef3977 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇ ((((y ◇ y) ◇
      ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇
      (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ x) := by
    first | exact superpose ef2174 ef3927 | exact superpose ef3927 ef2174
  have ef4002 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((y ◇ ((((y ◇ y) ◇
      ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (x ◇
      ((x ◇ (y ◇ y)) ◇ y)))) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) := by
    first | exact superpose ef247 ef3977 | exact superpose ef3977 ef247
  have ef4016 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ ((y ◇ (y ◇ y)) ◇ (((((y ◇ y) ◇
      ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (x ◇
      ((x ◇ (y ◇ y)) ◇ y))) ◇ (((y ◇ y) ◇ x) ◇ x))) := by
    first | exact superpose ef2171 ef4002 | exact superpose ef4002 ef2171
  have ef4030 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ (y ◇
      ((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (x ◇ ((x ◇ (y ◇ y)) ◇ y))))))) := by
    first | exact superpose ef2876 ef4016 | exact superpose ef4016 ef2876
  have ef4044 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (x ◇
      ((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (x ◇ ((x ◇ (y ◇ y)) ◇ y))))))) := by
    first | exact superpose ef2171 ef4030 | exact superpose ef4030 ef2171
  have ef4058 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (x ◇
      ((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (x ◇ ((x ◇ (y ◇ y)) ◇ y))))))) := by
    first | exact superpose ef2174 ef4044 | exact superpose ef4044 ef2174
  have ef4072 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ ((x ◇ x) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇
      ((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) := by
    first | exact superpose ef2876 ef4058 | exact superpose ef4058 ef2876
  have ef4086 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ (x ◇ ((((x ◇ x) ◇ (y ◇ y)) ◇ y) ◇
      ((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (((y ◇ y) ◇ y) ◇ y)))))) := by
    first | exact superpose ef2174 ef4072 | exact superpose ef4072 ef2174
  have ef4100 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ (x ◇ (y ◇ (y ◇
      (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y))))))))) := by
    first | exact superpose ef2876 ef4086 | exact superpose ef4086 ef2876
  have ef4114 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ (x ◇ (y ◇
      (((y ◇ y) ◇ (((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (x ◇ x)) ◇ y)) ◇
      y))))) := by
    first | exact superpose ef2898 ef4100 | exact superpose ef4100 ef2898
  have ef4128 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ (y ◇ (y ◇
      (((y ◇ y) ◇ (((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (x ◇ x)) ◇ y)) ◇
      x))))) := by
    first | exact superpose ef1996 ef4114 | exact superpose ef4114 ef1996
  have ef4142 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ (y ◇ (y ◇
      (((y ◇ y) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ ((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y))))) ◇
      x))))) := by
    first | exact superpose ef196 ef4128 | exact superpose ef4128 ef196
  have ef4156 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ (y ◇ (y ◇
      ((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ (x ◇ (y ◇ y)))) ◇
      (x ◇ x)))))) := by
    first | exact superpose ef247 ef4142 | exact superpose ef4142 ef247
  have ef4170 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ (y ◇ (y ◇
      ((((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ x) ◇
      (((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ (x ◇ (y ◇ y))) ◇ x)))))) := by
    first | exact superpose ef2171 ef4156 | exact superpose ef4156 ef2171
  have ef4184 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (y ◇ (y ◇
      (((x ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))))) ◇
      (((y ◇ y) ◇ ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇ x)) ◇
      y)))) := by
    first | exact superpose ef3172 ef4170 | exact superpose ef4170 ef3172
  have ef4198 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ (((((y ◇ y) ◇
      ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇ y)) ◇
      x) ◇ y) ◇ (x ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))))))) := by
    first | exact superpose ef17 ef4184 | exact superpose ef4184 ef17
  have ef4212 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ ((((x ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)))) ◇ x) ◇ x) ◇ (y ◇ ((y ◇
      y) ◇
      ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇
      y))))) := by
    first | exact superpose ef2115 ef4198 | exact superpose ef4198 ef2115
  have ef4226 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ ((((x ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)))) ◇ x) ◇ y) ◇ (x ◇ ((y ◇
      y) ◇
      ((y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) ◇
      y))))) := by
    first | exact superpose ef2171 ef4212 | exact superpose ef4212 ef2171
  have ef4240 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (x ◇ ((((x ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)))) ◇ x) ◇ x) ◇
      ((((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y)) ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef3489 ef4226 | exact superpose ef4226 ef3489
  have ef4254 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ y ◇ (y ◇ ((((x ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)))) ◇ x) ◇
      (((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y)) ◇ (y ◇ y))) ◇ (x ◇ x))) := by
    first | exact superpose ef1957 ef4240 | exact superpose ef4240 ef1957
  have ef4268 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇
      ((x ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)))) ◇ x))) ◇ y) ◇
      y := by
    first | exact superpose ef3172 ef4254 | exact superpose ef4254 ef3172
  have ef4282 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))))) ◇ (y ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ y))) := by
    first | exact superpose ef3139 ef4268 | exact superpose ef4268 ef3139
  have ef4296 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)))) ◇ ((x ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)))) ◇ x) := by
    first | exact superpose ef3145 ef4282 | exact superpose ef4282 ef3145
  have ef4310 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((x ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ x) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))))) ◇ ((((x ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y))) ◇ (y ◇ y)) := by
    first | exact superpose ef3144 ef4296 | exact superpose ef4296 ef3144
  have ef4324 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)))) ◇ ((y ◇ y) ◇
      (((y ◇ y) ◇ x) ◇ x)) := by
    first | exact superpose ef895 ef4310 | exact superpose ef4310 ef895
  have ef4338 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (((((y ◇ y) ◇ x) ◇ x) ◇ y) ◇ (x ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y))) ◇ x) := by
    first | exact superpose ef3144 ef4324 | exact superpose ef4324 ef3144
  have ef4352 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((x ◇ y) ◇ (x ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y))) ◇ (((y ◇ y) ◇ x) ◇
      x)) := by
    first | exact superpose ef3764 ef4338 | exact superpose ef4338 ef3764
  have ef4366 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ (((y ◇ y) ◇ x) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)))))) := by
    first | exact superpose ef2876 ef4352 | exact superpose ef4352 ef2876
  have ef4380 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (y ◇ ((((x ◇ y) ◇ y) ◇ x) ◇ ((x ◇ y) ◇ (((x ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)))))) := by
    first | exact superpose ef2174 ef4366 | exact superpose ef4366 ef2174
  have ef4394 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (y ◇ ((((x ◇ y) ◇ y) ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇
      ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef3489 ef4380 | exact superpose ef4380 ef3489
  have ef4408 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (y ◇ ((((x ◇ y) ◇ y) ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ y)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ y)) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2171 ef4394 | exact superpose ef4394 ef2171
  have ef4422 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (y ◇ ((((x ◇ y) ◇ y) ◇ x) ◇ ((y ◇ y) ◇
      ((((x ◇ ((x ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ y)) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2174 ef4408 | exact superpose ef4408 ef2174
  have ef4436 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (y ◇ ((((x ◇ y) ◇ y) ◇ x) ◇
      ((((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y) ◇ y))) := by
    first | exact superpose ef1036 ef4422 | exact superpose ef4422 ef1036
  have ef4450 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ (((x ◇ y) ◇ y) ◇ x)) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ x) ◇ x)))) := by
    first | exact superpose ef17 ef4436 | exact superpose ef4436 ef17
  have ef4464 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((((y ◇ y) ◇ x) ◇ x) ◇ ((((x ◇ y) ◇ y) ◇ x) ◇
      ((x ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2876 ef4450 | exact superpose ef4450 ef2876
  have ef4478 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ ((((((y ◇ y) ◇ x) ◇ x) ◇ y) ◇ x) ◇
      ((x ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2174 ef4464 | exact superpose ef4464 ef2174
  have ef4492 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ ((((((y ◇ y) ◇ x) ◇ x) ◇ y) ◇ x) ◇
      ((x ◇ y) ◇ (((x ◇ x) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2171 ef4478 | exact superpose ef4478 ef2171
  have ef4506 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ ((((((y ◇ y) ◇ x) ◇ x) ◇ y) ◇ x) ◇
      (x ◇ ((((x ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2174 ef4492 | exact superpose ef4492 ef2174
  have ef4520 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (((y ◇ x) ◇ x) ◇
      ((((x ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))) ◇
      ((((y ◇ y) ◇ x) ◇ x) ◇ y) := by
    first | exact superpose ef1390 ef4506 | exact superpose ef4506 ef1390
  have ef4534 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((y ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ x)) ◇
      (((((x ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇
      (y ◇ x)) := by
    first | exact superpose ef3144 ef4520 | exact superpose ef4520 ef3144
  have ef4548 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ x) ◇ (y ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇
      ((((x ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2876 ef4534 | exact superpose ef4534 ef2876
  have ef4562 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇
      ((((x ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2171 ef4548 | exact superpose ef4548 ef2171
  have ef4576 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ (x ◇ ((x ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ x) ◇ y) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ x)))))) := by
    first | exact superpose ef2174 ef4562 | exact superpose ef4562 ef2174
  have ef4590 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ (x ◇ ((x ◇ y) ◇ (x ◇ (y ◇
      (((y ◇ y) ◇ x) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ x) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))))))))) := by
    first | exact superpose ef2876 ef4576 | exact superpose ef4576 ef2876
  have ef4604 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ (x ◇ ((x ◇ y) ◇
      (x ◇ ((x ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ x))) ◇ x)) ◇ y))))) := by
    first | exact superpose ef2898 ef4590 | exact superpose ef4590 ef2898
  have ef4618 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((x ◇ y) ◇ (x ◇ (y ◇
      (y ◇ ((x ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ x))) ◇ x)) ◇ (x ◇ x)))))) := by
    first | exact superpose ef2876 ef4604 | exact superpose ef4604 ef2876
  have ef4632 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ x) ◇
      (((x ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ x))) ◇ x)) ◇ (x ◇ x)) ◇
      (y ◇ (x ◇ y)))) := by
    first | exact superpose ef2876 ef4618 | exact superpose ef4618 ef2876
  have ef4646 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((y ◇ x) ◇
      (((x ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ x))) ◇ x)) ◇ y) ◇
      ((x ◇ x) ◇ (x ◇ y)))) := by
    first | exact superpose ef2171 ef4632 | exact superpose ef4632 ef2171
  have ef4660 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      ((((y ◇ (y ◇ x)) ◇ (x ◇ ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ x))) ◇ x))) ◇ y) ◇
      x) := by
    first | exact superpose ef1390 ef4646 | exact superpose ef4646 ef1390
  have ef4674 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (((x ◇ (x ◇ x)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ x)))) ◇
      (y ◇ (y ◇ (y ◇ x)))) := by
    first | exact superpose ef3139 ef4660 | exact superpose ef4660 ef3139
  have ef4688 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (((x ◇ (x ◇ x)) ◇ y) ◇
      ((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ x))) ◇ (y ◇ (y ◇ x)))) := by
    first | exact superpose ef2171 ef4674 | exact superpose ef4674 ef2171
  have ef4702 :
      (x ◇ ((x ◇ x) ◇ x)) ◇
      (x ◇ x) ≠ ((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y)) ◇
      (x ◇ x) := by
    first | exact superpose ef2898 ef4688 | exact superpose ef4688 ef2898
  have ef4716 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((x ◇ ((y ◇ y) ◇ x)) ◇ x) ◇
      ((((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y) ◇ y) := by
    first | exact superpose ef2115 ef4702 | exact superpose ef4702 ef2115
  have ef4730 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ ((y ◇ ((y ◇ y) ◇ x)) ◇ x) ◇
      ((((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y) ◇ x) := by
    first | exact superpose ef3764 ef4716 | exact superpose ef4716 ef3764
  have ef4744 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (y ◇ (y ◇ x)) ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ x) ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ x))) ◇ y) ◇ x) := by
    first | exact superpose ef2174 ef4730 | exact superpose ef4730 ef2174
  have ef4758 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (y ◇ (y ◇ x)) ◇
      (((x ◇ ((y ◇ y) ◇ x)) ◇ ((y ◇ y) ◇ x)) ◇ (y ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef3139 ef4744 | exact superpose ef4744 ef3139
  have ef4772 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ (y ◇ (y ◇ x)) ◇
      (((x ◇ ((y ◇ y) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef2171 ef4758 | exact superpose ef4758 ef2171
  have ef4786 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      ((((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ x))) := by
    first | exact superpose ef2174 ef4772 | exact superpose ef4772 ef2174
  have ef4800 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (x ◇ (y ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ x)) ◇ ((y ◇ y) ◇ x))))) := by
    first | exact superpose ef2876 ef4786 | exact superpose ef4786 ef2876
  have ef4814 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (x ◇ (y ◇ (x ◇ (((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ (y ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ x)))))))) := by
    first | exact superpose ef2876 ef4800 | exact superpose ef4800 ef2876
  have ef4828 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (x ◇ (y ◇ ((((x ◇ x) ◇ (y ◇ y)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ x))) ◇ y))) := by
    first | exact superpose ef1390 ef4814 | exact superpose ef4814 ef1390
  have ef4842 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (y ◇ (y ◇ ((((x ◇ x) ◇ (y ◇ y)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ x))) ◇ x))) := by
    first | exact superpose ef1996 ef4828 | exact superpose ef4828 ef1996
  have ef4855 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (y ◇ (y ◇ ((x ◇ ((y ◇ (y ◇ x)) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ y))))) ◇ (y ◇ y)))) := by
    first | exact superpose ef247 ef4842 | exact superpose ef4842 ef247
  have ef4867 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (y ◇ (y ◇ ((x ◇ y) ◇ (((y ◇ (y ◇ x)) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ y)))) ◇ y)))) := by
    first | exact superpose ef1957 ef4855 | exact superpose ef4855 ef1957
  have ef4879 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (y ◇ (((x ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (x ◇ y)) ◇ (y ◇ (y ◇ x)))) := by
    first | exact superpose ef17 ef4867 | exact superpose ef4867 ef17
  have ef4890 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇
      (y ◇ (((x ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)))) := by
    first | exact superpose ef2171 ef4879 | exact superpose ef4879 ef2171
  have ef4900 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((((y ◇ y) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ y)))) ◇ x) ◇ x) := by
    first | exact superpose ef1390 ef4890 | exact superpose ef4890 ef1390
  have ef4910 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((((y ◇ y) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ (y ◇ y))) := by
    first | exact superpose ef3139 ef4900 | exact superpose ef4900 ef3139
  have ef4920 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((((y ◇ y) ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ y))) := by
    first | exact superpose ef2171 ef4910 | exact superpose ef4910 ef2171
  have ef4930 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (y ◇ (x ◇ (y ◇ (((y ◇ y) ◇ (x ◇ x)) ◇ (x ◇ x))))) := by
    first | exact superpose ef2876 ef4920 | exact superpose ef4920 ef2876
  have ef4940 :
      (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (y ◇ (x ◇ (y ◇ (((y ◇ y) ◇ x) ◇ ((x ◇ x) ◇ x))))) := by
    first | exact superpose ef2171 ef4930 | exact superpose ef4930 ef2171
  have ef4950 : (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ (y ◇ (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ y))) := by
    first | exact superpose ef2898 ef4940 | exact superpose ef4940 ef2898
  have ef4960 : (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) ≠ x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef17 ef4950 | exact superpose ef4950 ef17
  have ef4970 : (x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) ≠ x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef237 ef4960 | exact superpose ef4960 ef237
  subsumption ef4970 ef2174

theorem Equation3482_termDefinableFromFin_Equation898 : Law3482.TermDefinableFromFin Law898 := by
  intro G _ M hGL
  have h : Equation898 G := Law898.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x (M.op (M.op x x) y)) (M.op x y))⟩, ?_, ?_⟩
  · rw [@Law3482.models_iff]
    exact fun x y ↦ @aux898_3482 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 1))) (tm (Term.var 0) (Term.var 1))), rfl⟩

/-- Equation 4290 `x ◇ (x ◇ y) = y ◇ (x ◇ x)` is term-definable from equation 1117
`x = y ◇ ((y ◇ (x ◇ z)) ◇ z)` over finite magmas, via the term `x □ y := (x ◇ (y ◇ x)) ◇ x`. -/
private theorem aux1117_4290 [Finite G] [Magma G] (h : Equation1117 G) (x y : G) :
    (x ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ x)) ◇ x = (y ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ y)) ◇ y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ ((b ◇ a) ◇ c)) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((b ◇ z) ◇ c)) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have ef6 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef8 :
      (x ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ x)) ◇ x ≠ (y ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ y)) ◇ y := mod_symm nh
  have ef10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) ◇ X2 = (X1 ◇ (X0 ◇ X3)) ◇ X3 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef46 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) ◇ X3 = (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4)) ◇ X4 := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef73 (X0 : G) :
      (x ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ x)) ◇ x ≠ (y ◇ (((x ◇ (x ◇ X0)) ◇ X0) ◇ y)) ◇ y := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef77 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ (X1 ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X4)) ◇ X4 = X3 := by
    first | exact superpose ef10 ef7 | exact superpose ef7 ef10
  have ef125 (X0 X1 : G) :
      (x ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ x)) ◇ x ≠ (y ◇ (((x ◇ X0) ◇ ((x ◇ (X0 ◇ X1)) ◇ X1)) ◇ y)) ◇
      y := by
    first | exact superpose ef6 ef73 | exact superpose ef73 ef6
  have ef434 (X0 X1 X2 : G) :
      (x ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ x)) ◇
      x ≠ (y ◇ ((X0 ◇ ((x ◇ (((x ◇ (X0 ◇ X1)) ◇ X1) ◇ X2)) ◇ X2)) ◇ y)) ◇ y := by
    first | exact superpose ef6 ef125 | exact superpose ef125 ef6
  have ef4724 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X4) ◇ X5)) ◇ X5 = (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X6)) ◇ X6 := by
    first | exact superpose ef77 ef46 | exact superpose ef46 ef77
  have ef7564 (X0 X1 : G) :
      (x ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ x)) ◇ x ≠ (x ◇ (((x ◇ (y ◇ X0)) ◇ X0) ◇ X1)) ◇ X1 := by
    first | exact superpose ef7 ef434 | exact superpose ef434 ef7
  subsumption ef7564 ef4724

theorem Equation4290_termDefinableFromFin_Equation1117 : Law4290.TermDefinableFromFin Law1117 := by
  intro G _ M hGL
  have h : Equation1117 G := Law1117.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x (M.op y x)) x)⟩, ?_, ?_⟩
  · rw [@Law4290.models_iff]
    exact fun x y ↦ @aux1117_4290 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 1) (Term.var 0))) (Term.var 0)), rfl⟩

/-- Equation 4369 `x ◇ (y ◇ z) = z ◇ (y ◇ x)` is term-definable from equation 1117
`x = y ◇ ((y ◇ (x ◇ z)) ◇ z)` over finite magmas, via the term `x □ y := (x ◇ (y ◇ x)) ◇ x`. -/
private theorem aux1117_4369 [Finite G] [Magma G] (h : Equation1117 G) (x y z : G) :
    (x ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ x)) ◇ x = (z ◇ (((y ◇ (x ◇ y)) ◇ y) ◇ z)) ◇ z := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ ((b ◇ a) ◇ c)) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((b ◇ z) ◇ c)) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have ef6 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef8 :
      (x ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ x)) ◇ x ≠ (z ◇ (((y ◇ (x ◇ y)) ◇ y) ◇ z)) ◇ z := mod_symm nh
  have ef10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) ◇ X2 = (X1 ◇ (X0 ◇ X3)) ◇ X3 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef46 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) ◇ X3 = (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4)) ◇ X4 := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef73 (X0 : G) :
      (x ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ x)) ◇ x ≠ (z ◇ (((y ◇ (x ◇ X0)) ◇ X0) ◇ z)) ◇ z := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef77 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ (X1 ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X4)) ◇ X4 = X3 := by
    first | exact superpose ef10 ef7 | exact superpose ef7 ef10
  have ef125 (X0 X1 : G) :
      (x ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ x)) ◇ x ≠ (z ◇ (((y ◇ X0) ◇ ((x ◇ (X0 ◇ X1)) ◇ X1)) ◇ z)) ◇
      z := by
    first | exact superpose ef6 ef73 | exact superpose ef73 ef6
  have ef434 (X0 X1 X2 : G) :
      (x ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ x)) ◇
      x ≠ (z ◇ ((X0 ◇ ((x ◇ (((y ◇ (X0 ◇ X1)) ◇ X1) ◇ X2)) ◇ X2)) ◇ z)) ◇ z := by
    first | exact superpose ef6 ef125 | exact superpose ef125 ef6
  have ef4724 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X4) ◇ X5)) ◇ X5 = (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X6)) ◇ X6 := by
    first | exact superpose ef77 ef46 | exact superpose ef46 ef77
  have ef7564 (X0 X1 : G) :
      (x ◇ (((y ◇ (z ◇ y)) ◇ y) ◇ x)) ◇ x ≠ (x ◇ (((y ◇ (z ◇ X0)) ◇ X0) ◇ X1)) ◇ X1 := by
    first | exact superpose ef7 ef434 | exact superpose ef434 ef7
  subsumption ef7564 ef4724

theorem Equation4369_termDefinableFromFin_Equation1117 : Law4369.TermDefinableFromFin Law1117 := by
  intro G _ M hGL
  have h : Equation1117 G := Law1117.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x (M.op y x)) x)⟩, ?_, ?_⟩
  · rw [@Law4369.models_iff]
    exact fun x y z ↦ @aux1117_4369 G _ M h x y z
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 1) (Term.var 0))) (Term.var 0)), rfl⟩

end Law.MagmaLaw
